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
#include <fst/extensions/pdt/paren-data.h>
#include <fst/extensions/pdt/inside-outside.h>

#include <tr1/unordered_set>
using std::tr1::unordered_set;
#include <tr1/unordered_map>
using std::tr1::unordered_map;
using std::tr1::unordered_multimap;
#include <utility>
using std::make_pair;
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
                          bool uniq = false,
                          bool kp = false) :
      nshortest(n), max_pop(pop_limit), unique(uniq),
      keep_parentheses(kp) {}
};

namespace pdt {
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
                        item1, keep_parens ? arc1.ilabel : 0, keep_parens ? arc1.olabel : 0,
                        item2, keep_parens ? arc2.ilabel : 0, keep_parens ? arc2.olabel : 0);
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
    ItemId item1;
    Label ilabel1, olabel1;
    ItemId item2;
    Label ilabel2, olabel2;

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
        start_it_ = state_it_->second.begin();
    }

    ItemIterator(const PdtNShortestPathData<Arc> &nspdata,
                 StateId start, StateId state) :
        start_(start), nspdata_(nspdata),
        state_it_(nspdata.groups_.find(state)), start_it_() {
      if (state_it_ != nspdata.groups_.end())
        start_it_ = state_it_->second.find(start);
    }

    bool Done() {
      return state_it_ == nspdata_.groups_.end() ||
          start_it_ == state_it_->second.end() ||
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
      id = items_.size();
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
      return state_it_->second.count(start);
  }

  const Item &GetItem(ItemId id) {
    return items_[id];
  }

  void GetPathLabels(const Item &bottom, vector<pair<Label, Label> > *output) {
    output->clear();
    Traverse(bottom.parent, output);
  }

  void Traverse(const ItemParent &parent, vector<pair<Label, Label> > *output);

  vector<Item> items_;
  unordered_map<StateId, unordered_multimap<StateId, ItemId> > groups_;

  friend class PdtNShortestPath<Arc>;
};

template <class Arc>
void PdtNShortestPathData<Arc>::Traverse(const ItemParent &parent, vector<pair<Label, Label> > *output) {
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

template <class Arc>
class PdtNShortestPath {
 public:
  PdtNShortestPath(const Fst<Arc> &ifst,
                   const vector<pair<typename Arc::Label, typename Arc::Label> > &parens,
                   const PdtNShortestPathOptions &opts) :
      ifst_(ifst.Copy()), ofst_(NULL), parens_(parens),
      opts_(opts), error_(false), n_found_(0), n_enqueued_(0), heap_(NULL),
      pdata_(ifst, parens) {
    if ((Weight::Properties() & (kPath | kRightSemiring | kLeftSemiring)) !=
        (kPath | kRightSemiring | kLeftSemiring)) {
      FSTERROR() << "PdtNShortestPath: Weight needs to have the path"
                 << " property and be right distributive: " << Weight::Type();
      error_ = true;
    }
    pdata_.Init();
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

  typedef Heap<Item, typename NspData::ItemCompare, false> PriorityQueue;


  // Private methods; all methods accessing `ifst_' assume it is not
  // empty (i.e. ifst_->Start() != kNoStateId).
  void ClearFst(MutableFst<Arc> *ofst);
  void PreComputeHeuristics();
  void DoSearch();
  void EnqueueAxioms();
  void EnqueueAxiom(StateId s);
  void Enqueue(StateId start, StateId state, Weight weight, ItemParent parent);
  void OutputPath(const Item &it);
  void ProcArc(const Item &item, ItemId item_id, const Arc &arc);
  void Scan(const Item &item, ItemId item_id, const Arc &arc);
  void Complete(const Item &item1, ItemId item1_id, const Arc &arc1,
                const Item &item2, ItemId item2_id, const Arc &arc2);
  void TryCompleteAsItem1(const Item &item1, ItemId item1_id,
                          Label paren_id, const Arc &arc1);
  void TryCompleteAsItem2(const Item &item2, ItemId item2_id,
                          Label paren_id, const Arc &arc2);

  // Data fields
  Fst<Arc> *ifst_;
  MutableFst<Arc> *ofst_;
  const vector<pair<Label, Label> > &parens_;
  PdtNShortestPathOptions opts_;
  bool error_;
  size_t n_found_;
  size_t n_enqueued_;
  PriorityQueue *heap_;
  PdtParenData<Arc> pdata_;
  OutsideChart<Arc> out_chart_;
  NspData theorems_;

  DISALLOW_COPY_AND_ASSIGN(PdtNShortestPath);
};

template <class Arc> inline
void PdtNShortestPath<Arc>::ClearFst(MutableFst<Arc> *ofst) {
  ofst_ = ofst;
  ofst->DeleteStates();
  ofst->SetInputSymbols(ifst_->InputSymbols());
  ofst->SetOutputSymbols(ifst_->OutputSymbols());
}

// Pre-computes the distance from the start (to the final) to (from)
// each state when the input is treated as a plain FST.
template <class Arc> inline
void PdtNShortestPath<Arc>::PreComputeHeuristics() {
  OutsideAlgo<Arc>(*ifst_, parens_, &pdata_).FillChart(&out_chart_);
  VLOG(0) << "Oustide score done";
}

// A* search
template <class Arc>
void PdtNShortestPath<Arc>::DoSearch() {
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
    } else if (item_id != NspData::kNoItemId && // item must be added
               item.state != NspData::kSuperfinal) { // there will not be out-going arcs from a superfinal
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
template <class Arc>
void PdtNShortestPath<Arc>::EnqueueAxioms() {
  typedef unordered_set<StateId> StateSet;
  StateSet axioms;
  axioms.insert(ifst_->Start());
  for (SIter siter(*ifst_); !siter.Done(); siter.Next()) {
    for (AIter aiter(*ifst_, siter.Value()); !aiter.Done(); aiter.Next()) {
      const Arc &arc = aiter.Value();
      Label open_paren = pdata_.OpenParenId(arc.ilabel);
      if (open_paren == arc.ilabel) // open paren
        axioms.insert(arc.nextstate);
    }
  }
  for (typename StateSet::const_iterator i = axioms.begin(); i != axioms.end(); ++i)
    EnqueueAxiom(*i);
}

template <class Arc> inline
void PdtNShortestPath<Arc>::EnqueueAxiom(StateId s) {
  Enqueue(s, s, Weight::One(), ItemParent::Axiom());
}

template <class Arc> inline
void PdtNShortestPath<Arc>::Enqueue(StateId start, StateId state, Weight weight, ItemParent parent) {
  pair<Weight, Weight> out = out_chart_.OutsideWeight(start, state);
  Item it = {
    start, state, weight,
    Times(out.first, Times(weight, out.second)),
    parent
  };
  heap_->Insert(it);
  ++n_enqueued_;
  if (n_enqueued_ % 10000 == 0) VLOG(0) << n_enqueued_ << " enqueued";
}

// Outputs the path induced by `it' to `ofst_'; all epsilon
// transitions are kept; if `opts_.keep_parentheses' is false,
// parentheses will also become epsilon (this actually happens in
// Complete()).
template <class Arc>
void PdtNShortestPath<Arc>::OutputPath(const Item &it) {
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

template <class Arc> inline
void PdtNShortestPath<Arc>::ProcArc(const Item &item, ItemId item_id, const Arc &arc) {
  Label open_paren = pdata_.OpenParenId(arc.ilabel);
  if (open_paren == kNoLabel)           // lexical arc
    Scan(item, item_id, arc);
  else if (open_paren == arc.ilabel)    // open paren
    TryCompleteAsItem1(item, item_id, open_paren, arc);
  else                                  // close paren
    TryCompleteAsItem2(item, item_id, open_paren, arc);
}

template <class Arc> inline
void PdtNShortestPath<Arc>::Scan(const Item &item, ItemId item_id, const Arc &arc) {
  Enqueue(item.start, arc.nextstate,
          Times(item.weight, arc.weight),
          ItemParent::Scan(item_id, arc));
}

template <class Arc> inline
void PdtNShortestPath<Arc>::Complete(const Item &item1, ItemId item1_id, const Arc &arc1,
                                     const Item &item2, ItemId item2_id, const Arc &arc2) {
  Enqueue(item1.start, arc2.nextstate,
          Times(item1.weight, Times(arc1.weight, Times (item2.weight, arc2.weight))),
          ItemParent::Complete(item1_id, arc1, item2_id, arc2, opts_.keep_parentheses));
}

// Rule (C) as it, arc, ?, ?? |- (it.start, ??.nextstate)
template <class Arc>
void PdtNShortestPath<Arc>::TryCompleteAsItem1(const Item &item1, ItemId item1_id,
                                               Label open_paren, const Arc &arc1) {
  StateId open_dest = arc1.nextstate;

  for (typename PdtParenData<Arc>::Iterator close_it = pdata_.FindClose(open_paren, open_dest);
       !close_it.Done(); close_it.Next()) {
    const typename PdtParenData<Arc>::FullArc &fa = close_it.Value();
    StateId close_src = fa.state;
    const Arc &arc2 = fa.arc;
    for (ItemIterator item2_iter(theorems_, open_dest, close_src);
         !item2_iter.Done(); item2_iter.Next()) {
      ItemId item2_id = item2_iter.Value();
      const Item &item2 = theorems_.GetItem(item2_id);
      Complete(item1, item1_id, arc1, item2, item2_id, arc2);
    }
  }
}

// Rule (C) as ?, ??, it, arc |- (?.start, arc.nextstate)
template <class Arc>
void PdtNShortestPath<Arc>::TryCompleteAsItem2(const Item &item2, ItemId item2_id,
                                               Label open_paren, const Arc &arc2) {
  StateId close_src = item2.state;

  for (typename PdtParenData<Arc>::Iterator open_it = pdata_.FindOpen(open_paren, close_src);
       !open_it.Done(); open_it.Next()) {
    const typename PdtParenData<Arc>::FullArc &fa = open_it.Value();
    StateId open_src = fa.state;
    const Arc &arc1 = fa.arc;
    for (ItemIterator item1_iter(theorems_, open_src);
         !item1_iter.Done(); item1_iter.Next()) {
      ItemId item1_id = item1_iter.Value();
      const Item &item1 = theorems_.GetItem(item1_id);
      Complete(item1, item1_id, arc1, item2, item2_id, arc2);
    }
  }
}

} // namespace pdt

template <class Arc>
size_t NShortestPath(const Fst<Arc> &ifst,
                     const vector<pair<typename Arc::Label,
                     typename Arc::Label> > &parens,
                     MutableFst<Arc> *ofst,
                     const PdtNShortestPathOptions &opts) {
  pdt::PdtNShortestPath<Arc> pnsp(ifst, parens, opts);
  return pnsp.NShortestPath(ofst);
}

template <class Arc>
size_t NShortestPath(const Fst<Arc> &ifst,
                     const vector<pair<typename Arc::Label,
                     typename Arc::Label> > &parens,
                     MutableFst<Arc> *ofst,
                     size_t n) {
  return NShortestPath(ifst, parens, ofst, PdtNShortestPathOptions(n));
}
} // namespace fst

#endif  // FST_EXTENSIONS_PDT_N_SHORTEST_PATH_H__
