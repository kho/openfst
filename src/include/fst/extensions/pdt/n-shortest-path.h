// n-shortest-path.h
//
// Author: wuke@cs.umd.edu (Wu Ke)
//
// \file
// Functions to find n shortest paths in a PDT.

#ifndef FST_EXTENSIONS_PDT_N_SHORTEST_PATH_H__
#define FST_EXTENSIONS_PDT_N_SHORTEST_PATH_H__

#include <fst/fst.h>
#include <fst/heap.h>
#include <fst/mutable-fst.h>
#include <fst/shortest-distance.h>

#include <tr1/unordered_set>
using std::tr1::unordered_set;
#include <tr1/unordered_map>
using std::tr1::unordered_map;
using std::tr1::unordered_multimap;
#include <utility>
using std::pair;
#include <vector>
using std::vector;

namespace fst {
struct PdtNShortestPathOptions {
  size_t nshortest;                     // how many paths to return
  size_t max_pop; // max number search states to pop for a unique pair of PDT states
  bool unique;  // TODO: only return paths with distinct input strings
  bool keep_parentheses;  // whether to keep parentheses in the output
  PdtNShortestPathOptions(size_t n,
                          size_t pop_limit = 0,
                          bool uniq = true,
                          bool kp = false) :
      nshortest(n), max_pop(pop_limit), unique(uniq),
      keep_parentheses(kp) {}
};

template <class Arc>
class PdtNShortestPathData {
 public:
  typedef typename Arc::StateId StateId;
  typedef typename Arc::Weight Weight;
  typedef typename Arc::Label Label;

  typedef int ItemId;
  static const ItemId kNoItemId = -1;

  struct ItemParent {
    static ItemParent Axiom() {
      return ItemParent(kAxiom);
    }

    static ItemParent Scan(ItemId item, const Arc &arc) {
      return ItemParent(kScan, item, arc.ilabel);
    }

    static ItemParent Complete(ItemId item1, const Arc &arc1, ItemId item2, const Arc &arc2) {
      return ItemParent(kComplete, item1, label1, item2, label2);
    }

    ItemParent(int8 r = kNoRule,
               ItemId it1 = kNoItemId, Label lb1 = kNoLabel,
               ItemId it2 = kNoItemId, Label lb2 = kNoLabel) :
        rule(r), item1(it1), item2(it2), label1(lb1), label2(lb2) {}

    static const int8 kNoRule = -1;
    static const int8 kAxiom = 0;
    static const int8 kScan = 1;
    static const int8 kComplete = 2;

    // Which rule is used?
    int8 rule;
    // Data
    ItemId item1, item2;
    Label label1, label2;
  };

  struct Item {
    StateId start, state;
    Weight weight, estimate;
    ItemParent parent;
  };

  struct ItemCompare {
    bool operator() (const Item &it1, const Item &it2) {
      return Plus(it1.estimate, it2.estimate) == it1.estimate;
    }
  };

  class ItemIterator {
   public:
    ItemIterator(StateId state);
    ItemIterator(StateId start, StateId state);

    bool Done();
    void Next();
    ItemId Value();
  };

  ItemId AddAxiom(StateId start, StateId state);
  ItemId AddScan(StateId start, StateId state, ItemId ant, const Arc &arc);
  ItemId AddComplete(StateId start, StateId state, ItemId ant1, const Arc &open, ItemId ant2, const Arc &close);

 private:
  vector<Item> items;
  unordered_multimap<StateId, unordered_multimap<StateId, ItemId> > groups;
  ItemId AddItem();
};

template <class Arc>
class PdtNShortestPath {
 public:
  PdtNShortestPath(const Fst<Arc> &ifst,
                   const vector<pair<Label, Label> > &parens,
                   const PdtNShortestPathOptions &opts) :
      ifst_(ifst.Copy()), ofst_(NULL), parens_(parens),
      nshortest_(opts.nshortest), max_pop_(opts.max_pop),
      unique_(opts.unique), keep_parens_(opts.keep_parentheses),
      error_(false), n_found_(0), n_enqueued_(0) {
    if ((Weight::Properties() & (kPath | kRightSemiring | kLeftSemiring))
        != (kPath | kRightSemiring | kLeftSemiring)) {
      FSTERROR() << "PdtNShortestPath: Weight needs to have the path"
                 << " property and be right distributive: " << Weight::Type();
      error_ = true;
    }
  }

  ~PdtNShortestPath() {
    delete ifst_;
  }

  size_t NShortestPath(MutableFst<Arc> *ofst) {
    ClearFst(ofst);

    if (ifst_->Start() == kNoStateId)
      return;

    PreComputeHeuristic();
    PreComputeBalance();
    DoSearch();

    if (error_) ofst->SetProperties(kError, kError);

    return n_found_;
  }


 private:
  typedef typename Arc::StateId StateId;
  typedef typename Arc::Weight Weight;
  typedef typename Arc::Label Label;

  typedef StateIterator< Fst<Arc> > SIter;
  typedef ArcIterator< Fst<Arc> > AIter;

  typedef PdtNShortestPathData<Arc> NspData;
  typedef typename NspData::Item Item;
  typedef typename NspData::ItemId ItemId;
  typedef typename NspData::ItemIterator ItemIterator;
  typedef typename NspData::ItemParent ItemParent;

  typedef unordered_map<Label, Label> ParenIdMap; // open/close paren -> paren id (index in `parens_')
  typedef unordered_multimap<Label, StateId> ParenStatesMap; // paren id -> states with out-going paren arcs

  typedef Heap<Item, typename NspData::ItemCompare, false> PriorityQueue;


  // Private methods; all methods accessing `ifst_' assume it is not
  // empty (i.e. ifst_->Start() != kNoStateId).

  void ClearFst(MutableFst<Arc> *ofst) {
    ofst_ = ofst;
    ofst->DeleteStates();
    ofst->SetInputSymbols(ifst_->InputSymbols());
    ofst->SetOutputSymbols(ifst_->OutputSymbols());
  }

  // Pre-computes the distance from the start (to the final) to (from)
  // each state when the input is treated as a plain FST.
  void PreComputeHeuristics() {
    // Compute shortest distance from the start to each state
    ShortestDistance(ifst_, &from_start_);
    if (from_start_.length() == 1 && !from_start_[0].Member())
      FSTERROR() << "PdtNShortestPath: failed to compute FST shortest distance" << endl;

    // Compute shortest distance to one of the final states from each state
    ShortestDistance(ifst_, &to_final_, true);
    if (to_final_.length() == 1 && !to_final_[0].Member())
      FSTERROR() << "PdtNShortestPath: failed to compute FST reverse shortest distance" << endl;
  }

  // Assigns paren id to open/close paren labels; then pre-computes the
  // source states of open/close paren arcs indexed by paren ids.
  void PreComputeBalance() {
    for (Label i = 0; i < parens_.size(); ++i) {
      const pair<Label, Label>  &p = parens_[i];
      paren_id_map_[p.first] = i;
      paren_id_map_[p.second] = i;
    }

    for (SIter siter(*ifst_); !siter.Done(); siter.Next()) {
      StateId s = siter.Value();
      for (AIter aiter(*ifst_, s); !aiter.Done(); aiter.Next()) {
        const Arc &arc = aiter.Value();
        ParenIdMap::const_iterator pit =
            paren_id_map_.find(arc.ilabel);
        if (pit != paren_id_map_.end()) { // is a paren
          Label paren_id = pit->second;
          if (arc.ilabel == parens_[paren_id].first) // open paren
            open_paren_.insert(make_pair(paren_id, s));
          else                            // close paren
            close_paren_.insert(make_pair(paren_id, s));
        }
      }
    }
  }

  // A* search
  void DoSearch() {
    PriorityQueue q;
    heap_ = &q;

    EnqueueAxioms();

    while (!q.Empty()) {
      Item item = q.Pop();
      if (item.start == ifst_->Start() &&
          ifst_->Final(item.state) != Weight::Zero()) { // goal item
        OutputPath(item);
        if (++n_found_ == nshortest_)
          break;
      }
      ItemId item_id = theorems_.AddItem(item);

      for (AIter aiter(*ifst_, item.state); !aiter.Done(); aiter.Next()) {
        const Arc &arc = aiter.Value();
        ParenIdMap::const_iterator pit = paren_id_map_.find(arc.ilabel);
        if (pit == paren_id_map_.end()) { // lexical arc
          Scan(item, item_id, arc);
        } else {                          // is a paren
          Label paren_id = pit->second;
          if (arc.ilabel == parens_[paren_id].first)   // open paren
            TryCompleteAsItem1(item, item_id, paren_id, arc);
          else                            // close paren
            TryCompleteAsItem2(item, item_id, paren_id, arc);
        }
      }
    }
  }

  // Enqueues all axioms of the form `p \leadsto p: 1` where p is the
  // start or has incoming arc with open paren.
  void EnqueueAxioms() {
    typedef unordered_set<StateId> StateSet;
    StateSet axioms;
    axioms.insert(ifst_->Start());
    for (SIter siter(*ifst_); !siter.Done(); siter.Next()) {
      for (AIter aiter(siter.Value()); !aiter.Done(); aiter.Next()) {
        const Arc &arc = aiter.Value();
        ParenIdMap::const_iterator pit =
            paren_id_map_.find(arc.ilabel);
        if (pit != paren_id_map_.end() &&
            arc.ilabel == parens_[pit->second].first) // open paren
          axioms.insert(arc.nextstate);
      }
    }
    for (StateSet::const_iterator i = axioms.begin(); i != axioms.end(); ++i)
      EnqueueAxiom(*i);
  }

  void Enqueue(StateId start, StateId state, Weight weight, ItemParent parent) {
    Item it = {
      start, state, weight,
      Times(from_start_[start], Times(weight, to_final_[state])),
      parent
    };
    heap_->Insert(it);
    ++n_enqueued_;
  }

  void EnqueueAxiom(StateId s) {
    Enqueue(s, s, Weight::One(), ItemParent::Axiom());
  }

  void OutputPath(const Item &it) {
    // TODO
  }

  void Scan(const Item &item, ItemId item_id, const Arc &arc) {
    Enqueue(item.start, arc.nextstate,
            Times(item.weight, arc.weight),
            ItemParent::Scan(item_id, arc));
  }

  void Complete(const Item &item1, ItemId item1_id, const Arc &arc1,
                const Item &item2, ItemId item2_id, const Arc &arc2) {
    Enqueue(item1.start, arc2.nextstate,
            Times(item1.weight, Times(arc1.weight, Times (item2.weight, arc2.weight))),
            ItemParent::Complete(item1_id, arc1, item2_id, arc2));
  }

  // Rule (C) as it, arc, ?, ?? |- (it.start, ??.nextstate)
  void TryCompleteAsItem1(const Item &item1, ItemId item1_id,
                          Label paren_id, const Arc &arc1) {
    StateId open_dest = arc1.nextstate;
    Label close_label = parens_[paren_id].second;

    for (ParenStatesMap::const_iterator close_it = close_paren_.find(paren_id);
         close_it != close_paren_.end() && close_it->first == paren_id;
         ++close_it) {
      StateId close_src = close_it->second;
      for (AIter arc2_aiter(*ifst_, close_src); !arc2_aiter.Done();
           arc2_aiter.Next()) {
        const Arc &arc2 = arc2_aiter.Value();
        if (arc2.ilabel == close_label) {
          for (ItemIterator item2_iter(theorems_, open_dest, close_src);
               !item2_iter.Done(); item2_iter.Next()) {
            ItemId item2_id = item2_iter.Value();
            const Item &item2 = theorems_.GetItem(item2_id);
            Complete(item1, item1_id, arc1, item2, item2_id, arc2);
          }
        }
      }
    }
  }

  // Rule (C) as ?, ??, it, arc |- (?.start, arc.nextstate)
  void TryCompleteAsItem2(const Item &item2, ItemId item2_id,
                          Label paren_id, const Arc &arc2) {
    StateId open_dest = item2.start;
    Label open_label = parens_[paren_id].first;

    for (ParenStatesMap::const_iterator open_it = open_paren_.find(paren_id);
         open_it != open_paren_.end() && open_it->first == paren_id;
         ++open_it) {
      StateId open_src = open_it->second;
      for (AIter arc1_iter(*ifst_, open_src); !arc1_iter.Done();
           arc1_iter.Next()) {
        const Arc &arc1 = arc1_iter.Value();
        if (arc1.ilabel = open_label && arc1.nextstate == open_dest) {
          for (ItemIterator item1_iter(theorems_, open_src);
               !item1_iter.Done(); item1_iter.Next()) {
            ItemId item1_id = item1_iter.Value();
            const Item &item1 = theorems_.GetItem(item1_id);
            Complete(item1, item1_id, arc1, item2, item2_id, arc2);
          }
        }
      }
    }
  }


  // Data fields
  Fst<Arc> *ifst_;
  MutableFst<Arc> *ofst_;
  const vector<pair<Label, Label> > &parens_;
  ParenIdMap paren_id_map_; // open/close paren -> paren id

  vector<Weight> from_start_, to_final_;

  // states with out-going open/close paren arcs; indexed by paren id
  ParenStatesMap open_paren_, close_paren_;

  size_t nshortest_, max_pop_;
  bool keep_parens_, unique_;

  bool error_;

  size_t n_found_;
  size_t n_enqueued_;

  NspData theorems_;
  PriorityQueue *heap_;

  DISALLOW_COPY_AND_ASSIGN(PdtNShortestPath);
};

};  // namespace fst

#endif  // FST_EXTENSIONS_PDT_N_SHORTEST_PATH_H__
