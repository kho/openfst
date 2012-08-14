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

template <class Arc> class PdtNShortestPath;

template <class Arc>
class PdtNShortestPathData {
 private:
  typedef typename Arc::StateId StateId;
  typedef typename Arc::Weight Weight;
  typedef typename Arc::Label Label;

  typedef int ItemId;
  static const ItemId kNoItemId = -1;
  static const StateId kSuperfinal = -2;

  class ItemParent {
   public:
    // Factory methods
    static ItemParent Axiom() {
      return ItemParent(kAxiom);
    }

    static ItemParent Scan(ItemId item, const Arc &arc) {
      return ItemParent(kScan, item, arc.ilabel, arc.olabel);
    }

    static ItemParent Complete(ItemId item1, const Arc &arc1,
                               ItemId item2, const Arc &arc2,
                               bool keep_parens = true) {
      return ItemParent(kComplete,
                        item1, keep_parens ? arc1.ilabel : 0, arc1.olabel,
                        item2, keep_parens ? arc2.ilabel : 0, arc2.olabel);
    }

   private:
    ItemParent(int8 r = kNoRule,
               ItemId it1 = kNoItemId, Label ilb1 = kNoLabel, Label olb1 = kNoLabel,
               ItemId it2 = kNoItemId, Label ilb2 = kNoLabel, Label olb2 = kNoLabel) :
        rule(r),
        item1(it1), ilabel1(ilb1), olabel1(olb1),
        item2(it2), ilabel2(ilb2), olabel2(olb2) {}

    static const int8 kNoRule = -1;
    static const int8 kAxiom = 0;
    static const int8 kScan = 1;
    static const int8 kComplete = 2;

    // Which rule is used?
    int8 rule;
    // Data
    ItemId item1, item2;
    Label ilabel1, ilabel2;
    Label olabel1, olabel2;

    friend class PdtNShortestPathData<Arc>;
  };

  struct Item {
    StateId start, state;
    Weight weight, priority;
    ItemParent parent;
  };

  struct ItemCompare {
    bool operator() (const Item &it1, const Item &it2) {
      return Plus(it1.priority, it2.priority) == it1.priority;
    }
  };

  class ItemIterator {
   public:
    ItemIterator(const PdtNShortestPathData<Arc> &nspdata, StateId state) :
        start_(kNoStateId), nspdata_(nspdata),
        state_it_(nspdata.groups_.find(state)), start_it_() {
      if (state_it_ != nspdata.groups_.end())
        start_it_ = state_it_->begin();
    }

    ItemIterator(const PdtNShortestPathData<Arc> &nspdata,
                 StateId start, StateId state) :
        start_(start), nspdata_(nspdata),
        state_it_(nspdata.groups_.find(state)), start_it_() {
      if (state_it_ != nspdata.groups_.end())
        start_it_ = state_it_->find(start);
    }

    bool Done() {
      return state_it_ == nspdata_.groups_.end() ||
          start_it_ == state_it_->end() ||
          (start_ != kNoStateId && start_it_->first != start_);
    }

    void Next() {
      ++start_it_;
    }

    ItemId Value() {
      return start_it_->second;
    }

   private:
    StateId start_;
    const PdtNShortestPathData<Arc> &nspdata_;
    typename unordered_map<StateId, unordered_multimap<StateId, ItemId> >::const_iterator state_it_;
    typename unordered_multimap<StateId, ItemId>::const_iterator start_it_;
  };

  ItemId AddItem(const Item &item, size_t limit = 0) {
    ItemId id = kNoItemId;
    if (!limit || CountItems(item.start, item.state) < limit) {
      id = items_.length();
      items_.push_back(item);
      groups_[item.state].insert(make_pair(item.start, id));
    }
    return id;
  }

  size_t CountItems(StateId start, StateId state) {
    typename unordered_map<StateId, unordered_multimap<StateId, ItemId> >::const_iterator
        state_it_ = groups_.find(state);
    if (state_it_ == groups_.end())
      return 0;
    else
      return state_it_->count(start);
  }

  const Item &GetItem(ItemId id) {
    return items_[id];
  }

  void GetPathLabels(const Item &bottom, vector<pair<Label, Label> > *output) {
    output->clear();
    Traverse(bottom.parent, output);
  }

  void Traverse(const ItemParent &parent, vector<pair<Label, Label> > *output) {
    switch (parent.rule) {
      case ItemParent::kAxiom:
        break;
      case ItemParent::kScan:
        Traverse(GetItem(parent.item1).parent, output);
        output->push_back(make_pair(parent.ilabel1, parent.olabel1));
        break;
      case ItemParent::kComplete:
        Traverse(GetItem(parent.item1).parent, output);
        output->push_back(make_pair(parent.ilabel1, parent.olabel1));
        Traverse(GetItem(parent.item2).parent, output);
        output->push_back(make_pair(parent.ilabel2, parent.olabel2));
        break;
      default:
        FSTERROR() << "PdtNShortestPathData::Traverse: invalid parent rule: `"
                   << parent.rule << "'";
    }
  }

  vector<Item> items_;
  unordered_map<StateId, unordered_multimap<StateId, ItemId> > groups_;

  friend class PdtNShortestPath<Arc>;
};

template <class Arc>
class PdtNShortestPath {
 public:
  PdtNShortestPath(const Fst<Arc> &ifst,
                   const vector<pair<typename Arc::Label, typename Arc::Label> > &parens,
                   const PdtNShortestPathOptions &opts) :
      ifst_(ifst.Copy()), ofst_(NULL), parens_(parens),
      opts_(opts), error_(false), n_found_(0), n_enqueued_(0), heap_(NULL) {
    if ((Weight::Properties() & (kPath | kRightSemiring | kLeftSemiring)) !=
        (kPath | kRightSemiring | kLeftSemiring)) {
      FSTERROR() << "PdtNShortestPath: Weight needs to have the path"
                 << " property and be right distributive: " << Weight::Type();
      error_ = true;
    }
  }

  ~PdtNShortestPath() {
    VLOG(1) << "# of input states: " << CountStates(*ifst_);
    VLOG(1) << "# of enqueued items: " << n_enqueued_;
    delete ifst_;
  }

  size_t NShortestPath(MutableFst<Arc> *ofst) {
    ClearFst(ofst);

    if (ifst_->Start() == kNoStateId)
      return 0;

    PreComputeHeuristics();
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
      FSTERROR() << "PdtNShortestPath: failed to compute reverse FST shortest distance" << endl;
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
        typename ParenIdMap::const_iterator pit =
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
      ItemId item_id = theorems_.AddItem(item, opts_.max_pop);
      if (item.start == ifst_->Start() && item.state == NspData::kSuperfinal) { // goal item
        OutputPath(item);
        if (++n_found_ == opts_.nshortest)
          break;
      } else if (item_id != NspData::kNoItemId) { // there will not be out-going arcs from a superfinal
        Weight rho = ifst_->Final(item.state);
        // If `item.state' is a final state, hallucinate a pseudo-arc
        // to the superfinal
        if (rho != Weight::Zero())
          ProcArc(item, item_id, Arc(0, 0, rho, NspData::kSuperfinal));
        for (AIter aiter(*ifst_, item.state); !aiter.Done(); aiter.Next())
          ProcArc(item, item_id, aiter.Value());
      }
    }

    heap_ = NULL;
  }

  // Enqueues all the axioms of the form `p \leadsto p: 1` where
  // either p is the start or it has an incoming arc with open paren.
  void EnqueueAxioms() {
    typedef unordered_set<StateId> StateSet;
    StateSet axioms;
    axioms.insert(ifst_->Start());
    for (SIter siter(*ifst_); !siter.Done(); siter.Next()) {
      for (AIter aiter(siter.Value()); !aiter.Done(); aiter.Next()) {
        const Arc &arc = aiter.Value();
        typename ParenIdMap::const_iterator pit =
            paren_id_map_.find(arc.ilabel);
        if (pit != paren_id_map_.end() &&
            arc.ilabel == parens_[pit->second].first) // open paren
          axioms.insert(arc.nextstate);
      }
    }
    for (typename StateSet::const_iterator i = axioms.begin(); i != axioms.end(); ++i)
      EnqueueAxiom(*i);
  }

  void EnqueueAxiom(StateId s) {
    Enqueue(s, s, Weight::One(), ItemParent::Axiom());
  }

  void Enqueue(StateId start, StateId state, Weight weight, ItemParent parent) {
    Item it = {
      start, state, weight,
      Times(from_start_[start],
            state == NspData::kSuperfinal ?
            weight : Times(weight, to_final_[state])),
      parent
    };
    heap_->Insert(it);
    ++n_enqueued_;
  }

  // Outputs the path induced by `it' to `ofst_'; all epsilon
  // transitions are kept; if `opts_.keep_parentheses' is false,
  // parentheses will also become epsilon (this actually happens in
  // Complete()).
  void OutputPath(const Item &it) {
    vector<pair<Label, Label> > path_label;
    theorems_.GetPathLabels(it, &path_label);
    if (path_label.empty()) {
      FSTERROR() << "PdtNShortestPath: trying to output empty path.";
      error_ = true;
    }
    if (opts_.unique)
      FSTERROR() << "PdtNShortestPath: unique path output is not implemented yet.";

    StateId src = ofst_->Start(), dest = kNoStateId;
    if (src == kNoStateId) {
      src = ofst_->AddState();
      ofst_->SetStart(src);
    }
    for (typename vector<pair<Label, Label> >::const_iterator i = path_label.begin();
         i != path_label.end(); ++i) {
        dest = ofst_->AddState();
        ofst_->AddArc(src, Arc(i->first, i->second, Weight::One(), dest));
        src = dest;
    }
    ofst_->SetFinal(src, it.weight);
  }

  void ProcArc(const Item &item, ItemId item_id, const Arc &arc) {
    typename ParenIdMap::const_iterator pit = paren_id_map_.find(arc.ilabel);
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

  void Scan(const Item &item, ItemId item_id, const Arc &arc) {
    Enqueue(item.start, arc.nextstate,
            Times(item.weight, arc.weight),
            ItemParent::Scan(item_id, arc));
  }

  void Complete(const Item &item1, ItemId item1_id, const Arc &arc1,
                const Item &item2, ItemId item2_id, const Arc &arc2) {
    Enqueue(item1.start, arc2.nextstate,
            Times(item1.weight, Times(arc1.weight, Times (item2.weight, arc2.weight))),
            ItemParent::Complete(item1_id, arc1, item2_id, arc2, opts_.keep_parentheses));
  }

  // Rule (C) as it, arc, ?, ?? |- (it.start, ??.nextstate)
  void TryCompleteAsItem1(const Item &item1, ItemId item1_id,
                          Label paren_id, const Arc &arc1) {
    StateId open_dest = arc1.nextstate;
    Label close_label = parens_[paren_id].second;

    for (typename ParenStatesMap::const_iterator close_it = close_paren_.find(paren_id);
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

    for (typename ParenStatesMap::const_iterator open_it = open_paren_.find(paren_id);
         open_it != open_paren_.end() && open_it->first == paren_id;
         ++open_it) {
      StateId open_src = open_it->second;
      for (AIter arc1_iter(*ifst_, open_src); !arc1_iter.Done();
           arc1_iter.Next()) {
        const Arc &arc1 = arc1_iter.Value();
        if (arc1.ilabel == open_label && arc1.nextstate == open_dest) {
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
  PdtNShortestPathOptions opts_;
  bool error_;
  size_t n_found_;
  size_t n_enqueued_;
  PriorityQueue *heap_;

  // These are default initialized.
  ParenIdMap paren_id_map_; // open/close paren -> paren id
  vector<Weight> from_start_, to_final_;
  // states with out-going open/close paren arcs; indexed by paren id
  ParenStatesMap open_paren_, close_paren_;
  NspData theorems_;

  DISALLOW_COPY_AND_ASSIGN(PdtNShortestPath);
};

};  // namespace fst

#endif  // FST_EXTENSIONS_PDT_N_SHORTEST_PATH_H__
