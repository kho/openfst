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
template <class Arc>
class OutsideHeuristic {
 public:
  typedef typename Arc::StateId StateId;
  typedef typename Arc::Weight InWeight;
  typedef typename Arc::Label Label;
  typedef typename OutWeightOp<InWeight>::OutWeight OutWeight;

  OutsideHeuristic(const Fst<Arc> &fst, const vector<pair<Label, Label> > &parens,
                   PdtParenData<Arc> *pdata) {
    InsideAlgo<Arc>(fst, parens, pdata).FillChart(&chart_);
    OutsideAlgo<Arc>(fst, parens, pdata).FillChart(&chart_);
  }

  InWeight Score(StateId start, StateId state, InWeight weight) {
    ItemId item = chart_.Find(start, state);
    OutWeight outside_weight = item == kNoItemId ?
        OutWeightOp<InWeight>::Zero() :
        chart_.GetOutsideWeight(item);
    // VLOG(0) << "Outside score: " << start << "~>" << state << ":" << weight;
    return OutWeightOp<InWeight>::MiddleTimes(outside_weight, weight);
  }

 private:
  InsideOutsideChart<Arc> chart_;
};


template <class Arc>
class ReverseInsideHeuristic {
 public:
  typedef typename Arc::StateId StateId;
  typedef typename Arc::Weight Weight;
  typedef typename Arc::Label Label;

  ReverseInsideHeuristic(const Fst<Arc> &fst, const vector<pair<Label, Label> > &parens,
                         PdtParenData<Arc> *pdata) :
      pdata_(pdata) {
    ReverseInsideAlgo<Arc>(fst, parens, pdata).FillChart(&chart_);
  }

  Weight Score(StateId start, StateId state, Weight weight) {
    typename CacheMap::const_iterator it = cache_.find(Span<Arc>(start, state));
    Weight ret(Weight::Zero());
    if (it == cache_.end()) {
      for (typename PdtParenData<Arc>::SubFinalIterator sfit = pdata_->FindSubFinal(start);
           !sfit.Done(); sfit.Next()) {
        StateId subfinal = sfit.Value();
        Weight d = chart_.GetWeight(chart_.Find(state, subfinal));
        ret = Plus(ret, d);
      }
      cache_[Span<Arc>(start, state)] = ret;
    } else {
      ret = it->second;
    }
    return Times(weight, ret);
  }

 private:
  typedef unordered_map<Span<Arc>, Weight> CacheMap;

  SpanWeightChart<Arc> chart_;
  CacheMap cache_;
  PdtParenData<Arc> *pdata_;
};

template <class Arc>
class ReverseDistance {
 public:
  typedef typename Arc::StateId StateId;
  typedef typename Arc::Weight Weight;
  typedef typename Arc::Label Label;

  ReverseDistance(const Fst<Arc> &fst, const vector<pair<Label, Label> > &parens,
                  PdtParenData<Arc> *pdata) {
    ReverseInsideAlgo<Arc>(fst, parens, pdata).FillChart(&chart_);
  }

  Weight Score(StateId state, StateId final, Weight weight) {
    ItemId item = chart_.Find(state, final);
    Weight dist = item == kNoItemId ? Weight::Zero() : chart_.GetWeight(item);
    return Times(weight, dist);
  }

 private:
  SpanWeightChart<Arc> chart_;
};

template <class Arc, template <class> class Heuristic> class PdtNShortestPath;

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

    template <class A> friend class PdtNShortestPathData;
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

  template <class A, template <class> class H> friend class PdtNShortestPath;
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

template <class Arc, template <class> class Heuristic>
class PdtNShortestPath {
 public:
  PdtNShortestPath(const Fst<Arc> &ifst,
                   const vector<pair<typename Arc::Label, typename Arc::Label> > &parens,
                   const PdtNShortestPathOptions &opts) :
      ifst_(ifst.Copy()), ofst_(NULL), parens_(parens),
      opts_(opts), error_(false), n_found_(0), n_enqueued_(0), heap_(NULL),
      pdata_(parens), heuristics_(NULL) {
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

    Heuristic<Arc> h(*ifst_, parens_, &pdata_);
    heuristics_ = &h;

    Timer::Get(0).Start();
    DoSearch();
    Timer::Get(0).Record("A* search");

    if (error_) ofst->SetProperties(kError, kError);

    heuristics_ = NULL;

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
  size_t n_enqueued_, n_dequeued_;
  PriorityQueue *heap_;
  PdtParenData<Arc> pdata_;
  NspData theorems_;
  Heuristic<Arc> *heuristics_;

  DISALLOW_COPY_AND_ASSIGN(PdtNShortestPath);
};

template <class Arc, template <class> class Heuristic> inline
void PdtNShortestPath<Arc, Heuristic>::ClearFst(MutableFst<Arc> *ofst) {
  ofst_ = ofst;
  ofst->DeleteStates();
  ofst->SetInputSymbols(ifst_->InputSymbols());
  ofst->SetOutputSymbols(ifst_->OutputSymbols());
}

// A* search
template <class Arc, template <class> class Heuristic>
void PdtNShortestPath<Arc, Heuristic>::DoSearch() {
  PriorityQueue q;
  heap_ = &q;

  n_enqueued_ = 0;
  n_dequeued_ = 0;

  EnqueueAxioms();

  while (!q.Empty()) {
    Item item = q.Pop();
    // VLOG(0) << "Dequeue " << item.start << "~>" << item.state << ":" << item.weight << "," << item.priority;
    ++n_dequeued_;
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

  VLOG(0) << "A* enq " << n_enqueued_ << " deq " << n_dequeued_ << " found " << n_found_;

  heap_ = NULL;
}

// Enqueues all the axioms of the form `p \leadsto p: 1` where
// either p is the start or it has an incoming arc with open paren.
template <class Arc, template <class> class Heuristic>
void PdtNShortestPath<Arc, Heuristic>::EnqueueAxioms() {
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

template <class Arc, template <class> class Heuristic> inline
void PdtNShortestPath<Arc, Heuristic>::EnqueueAxiom(StateId s) {
  Enqueue(s, s, Weight::One(), ItemParent::Axiom());
}

template <class Arc, template <class> class Heuristic> inline
void PdtNShortestPath<Arc, Heuristic>::Enqueue(StateId start, StateId state, Weight weight, ItemParent parent) {
  Weight priority = heuristics_->Score(start, state, weight);
  Item it = { start, state, weight, priority, parent };
  heap_->Insert(it);
  ++n_enqueued_;
}

// Outputs the path induced by `it' to `ofst_'; all epsilon
// transitions are kept; if `opts_.keep_parentheses' is false,
// parentheses will also become epsilon (this actually happens in
// Complete()).
template <class Arc, template <class> class Heuristic>
void PdtNShortestPath<Arc, Heuristic>::OutputPath(const Item &it) {
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

template <class Arc, template <class> class Heuristic> inline
void PdtNShortestPath<Arc, Heuristic>::ProcArc(const Item &item, ItemId item_id, const Arc &arc) {
  Label open_paren = pdata_.OpenParenId(arc.ilabel);
  if (open_paren == kNoLabel)           // lexical arc
    Scan(item, item_id, arc);
  else if (open_paren == arc.ilabel)    // open paren
    TryCompleteAsItem1(item, item_id, open_paren, arc);
  else                                  // close paren
    TryCompleteAsItem2(item, item_id, open_paren, arc);
}

template <class Arc, template <class> class Heuristic> inline
void PdtNShortestPath<Arc, Heuristic>::Scan(const Item &item, ItemId item_id, const Arc &arc) {
  Enqueue(item.start, arc.nextstate,
          Times(item.weight, arc.weight),
          ItemParent::Scan(item_id, arc));
}

template <class Arc, template <class> class Heuristic> inline
void PdtNShortestPath<Arc, Heuristic>::Complete(const Item &item1, ItemId item1_id, const Arc &arc1,
                                                const Item &item2, ItemId item2_id, const Arc &arc2) {
  Enqueue(item1.start, arc2.nextstate,
          Times(item1.weight, Times(arc1.weight, Times (item2.weight, arc2.weight))),
          ItemParent::Complete(item1_id, arc1, item2_id, arc2, opts_.keep_parentheses));
}

// Rule (C) as it, arc, ?, ?? |- (it.start, ??.nextstate)
template <class Arc, template <class> class Heuristic>
void PdtNShortestPath<Arc, Heuristic>::TryCompleteAsItem1(const Item &item1, ItemId item1_id,
                                                          Label open_paren, const Arc &arc1) {
  StateId open_dest = arc1.nextstate;

  for (typename PdtParenData<Arc>::Iterator close_it = pdata_.FindClose(open_paren, open_dest);
       !close_it.Done(); close_it.Next()) {
    const FullArc<Arc> &fa = close_it.Value();
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
template <class Arc, template <class> class Heuristic>
void PdtNShortestPath<Arc, Heuristic>::TryCompleteAsItem2(const Item &item2, ItemId item2_id,
                                                          Label open_paren, const Arc &arc2) {
  StateId close_src = item2.state;

  for (typename PdtParenData<Arc>::Iterator open_it = pdata_.FindOpen(open_paren, close_src);
       !open_it.Done(); open_it.Next()) {
    const FullArc<Arc> &fa = open_it.Value();
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

template <class Arc>
class NewNShortestPath {
 public:
  typedef typename Arc::StateId StateId;
  typedef typename Arc::Weight Weight;
  typedef typename Arc::Label Label;

  NewNShortestPath(const Fst<Arc> &ifst, const vector<pair<Label, Label> > &parens,
                   const PdtNShortestPathOptions &opts) :
      ifst_(ifst.Copy()), parens_(parens), opts_(opts) {}

  // Extracts n shortest paths into `ofst` following the given options
  // at construction and returns the number of paths found.
  size_t NShortestPath(MutableFst<Arc> *ofst) {
    return NShortestPathImpl(ofst);
  }

 private:
  //
  // Back pointer between items.
  //
  struct Parent {
    Parent() :
        item1(kNoItemId), item2(kNoItemId) {}

    Parent(ItemId item, const Arc &arc) :
        item1(item), item2(kNoItemId), arc1(arc) {}

    Parent(ItemId it1, const Arc &ar1, ItemId it2, const Arc &ar2) :
        item1(it1), item2(it2), arc1(ar1), arc2(ar2) {}

    Parent(ItemId it1, const Arc &ar1, const Arc &ar2, StateId st) :
        item1(it1), item2(kPromiseItem), arc1(ar1), arc2(ar2), src2(st) {}

    static Parent Root() {
      return Parent();
    }

    static Parent LexParent(ItemId item, const Arc &arc) {
      return Parent(item, arc);
    }

    static Parent ParParent(ItemId item1, const Arc &arc1, ItemId item2, const Arc &arc2) {
      return Parent(item1, arc1, item2, arc2);
    }

    static Parent PromiseParent(ItemId item1, const Arc &arc1, StateId src2, const Arc &arc2) {
      return Parent(item1, arc1, arc2, src2);
    }

    bool IsRoot() const {
      return item1 == kNoItemId && item2 == kNoItemId;
    }

    bool IsLexParent() const {
      return item1 != kNoItemId && item2 == kNoItemId;
    }

    bool IsParParent() const {
      return item1 != kNoItemId && item2 != kNoItemId && item2 != kPromiseItem;
    }

    bool IsPromiseParent() const {
      return item1 != kNoItemId && item2 == kPromiseItem;
    }

    ItemId item1, item2;
    Arc arc1, arc2;
    StateId src2;
  };

  //
  // A proof item, consists of the span of the balanced path, the
  // weight, the estimated priority and its parent. In addition, goal
  // items are linked with `next`.
  //
  struct Item {
    StateId start, state;
    Weight weight, priority;
    Parent parent;
    // Provides link to next item with same (start, state),
    // when (start, state) is goal of some sub-prover, it stores
    //
    // - It is the item's ItemId if this is the last goal
    // item the prover has found so far and the prover is not done
    // yet.
    //
    // - It is kNoItemId if this the last goal item the prover has
    // found and the prover has finished.
    //
    // - Otherwise, it is the ItemId of next goal item.
    //
    // When (start, state) is not a goal, it is always kNoItemId.
    //
    // It is the prover's job to update the field.
    ItemId next;

    Item(StateId p, StateId q, Weight w, Weight h, Parent b, ItemId n = kNoItemId) :
        start(p), state(q), weight(w), priority(h), parent(b), next(n) {}
  };

  //
  // The collection of items
  //
  class Chart {
   public:
    ItemId AddItem(StateId start, StateId state,
                   Weight weight, Weight priority,
                   Parent parent) {
      ItemId id = items_.size();
      items_.push_back(Item(start, state, weight, priority, parent));
      return id;
    }

    const Item &GetItem(ItemId id) const {
      return items_[id];
    }

    void SetNext(ItemId id, ItemId next) {
      items_[id].next = next;
    }

    void ForcePromise(ItemId id, ItemId id2) {
      items_[id].parent.item2 = id2;
    }

    void ExtractPath(ItemId id, MutableFst<Arc> *ofst) {
      vector<const Arc *> l;
      Traverse(id, &l);
      StateId p = ofst->Start();
      if (p == kNoStateId) {
        p = ofst->AddState();
        ofst->SetStart(p);
      }
      for (size_t i = 0; i < l.size(); ++i) {
        const Arc &arc = *l[i];
        StateId q = ofst->AddState();
        ofst->AddArc(p, Arc(arc.ilabel, arc.olabel, Weight::One(), q));
        p = q;
      }
      ofst->SetFinal(p, GetItem(id).weight);
    }

   private:
    void Traverse(ItemId id, vector<const Arc *> *output) {
      const Parent &parent = GetItem(id).parent;
      if (parent.IsLexParent()) {
        Traverse(parent.item1, output);
        output->push_back(&parent.arc1);
      } else if (parent.IsParParent()) {
        Traverse(parent.item1, output);
        // output->push_back(&parent.arc1);
        Traverse(parent.item2, output);
        // output->push_back(&parent.arc2);
      }
    }

    vector<Item> items_;
  };

  //
  // The collection of data used in provers.
  //
  struct Closure {
    const Fst<Arc> *fst;
    PdtParenData<Arc> pdata;
    ReverseDistance<Arc> heuristic;
    Chart chart;
    size_t n_enqueued_, n_dequeued_;

    // Note: we assume that after construction pdata has precise
    // knowledge of open/close-paren pairs.
    Closure(const Fst<Arc> &f, const vector<pair<Label, Label> > parens) :
        fst(f.Copy()), pdata(parens), heuristic(f, parens, &pdata),
        n_enqueued_(0), n_dequeued_(0) {}
  };

  //
  // Rank ItemId's by their priority
  //
  struct ItemCompare {
    ItemCompare(Closure *data) :
        data_(data) {}

    bool operator() (ItemId id1, ItemId id2) {
      Weight p1 = data_->chart.GetItem(id1).priority,
          p2 = data_->chart.GetItem(id2).priority;
      return Plus(p1, p2) == p1;
    }

    Closure *data_;
  };

  class ProverPool;

  //
  // The prover that incrementally finds n shortest paths between
  // `start` and `final`.
  //
  class Prover {
   public:
    Prover(StateId start, StateId final, Closure *data, ProverPool *pool) :
        start_(start), final_(final), data_(data), pool_(pool), queue_(ItemCompare(data)),
        head_found_(false), head_(kNoItemId), n_dequeued_(0) {
      Enqueue(start_, Weight::One(), Parent::Root());
    }

    // Finds the next accepting path; returns its Itemid if found,
    // kNoItemId otherwise.
    ItemId Advance(ItemId last_goal) {
      ItemId this_goal = FindNext();
      if (last_goal != kNoItemId)
        data_->chart.SetNext(last_goal, this_goal);
      if (this_goal != kNoItemId)
        data_->chart.SetNext(this_goal, this_goal);
      return this_goal;
    }

    // Returns the ItemId representing the shortest accepting path.
    ItemId Head() {
      if (!head_found_) {
        head_ = Advance(kNoItemId);
        head_found_ = true;
      }
      return head_;
    }

   private:
    typedef Heap<ItemId, ItemCompare, false> PriorityQueue;

    ItemId FindNext();
    void ProcArc(ItemId, const Arc &);
    void Scan(ItemId, const Arc &);
    void Promise(ItemId, const Arc &, StateId, const Arc &);
    void Complete(ItemId, const Arc &, ItemId, const Arc &);
    void Enqueue(StateId, Weight, Parent);
    ItemId Dequeue();

    StateId start_, final_;
    Closure *data_;
    ProverPool *pool_;
    PriorityQueue queue_;
    bool head_found_;
    ItemId head_;
    size_t n_enqueued_, n_dequeued_;
  };

  //
  // A collection of provers; other provers query this to get a hold
  // of other provers in order to get subgraph paths.
  //
  class ProverPool {
   public:
    ProverPool(Closure *data) :
        data_(data) {}

    ~ProverPool() {
      for (typename unordered_map<Span<Arc>, Prover *>::iterator it = pool_.begin();
           it != pool_.end(); ++it)
        delete it->second;
    }

    Prover *GetProver(StateId start, StateId final) {
      Span<Arc> sp(start, final);
      typename unordered_map<Span<Arc>, Prover *>::iterator it = pool_.find(sp);
      Prover *ret = NULL;
      if (it == pool_.end()) {
        ret = new Prover(start, final, data_, this);
        pool_[sp] = ret;
      } else {
        ret = it->second;
      }
      return ret;
    }

   private:
    Closure *data_;
    unordered_map<Span<Arc>, Prover *> pool_;
  };


  size_t NShortestPathImpl(MutableFst<Arc> *ofst) {
    ofst->DeleteStates();
    ofst->SetInputSymbols(ifst_->InputSymbols());
    ofst->SetOutputSymbols(ifst_->OutputSymbols());

    if (ifst_->Start() == kNoStateId)
      return 0;

    size_t n_found = 0;
    Closure data(*ifst_, parens_);
    ProverPool provers(&data);
    Prover *top = provers.GetProver(ifst_->Start(), kSuperfinal);
    ItemId it = kNoItemId;
    Timer::Get(0).Start();
    while (n_found < opts_.nshortest) {
      // Prove next path
      it = top->Advance(it);
      if (it == kNoItemId)
        break;
      ++n_found;
      // Output path
      data.chart.ExtractPath(it, ofst);
    }
    Timer::Get(0).Record("Reverse A*");

    VLOG(0) << "Lazy enq " << data.n_enqueued_ << " deq " << data.n_dequeued_ << " found " << n_found;
    return n_found;
  }

  const Fst<Arc> *ifst_;
  const vector<pair<Label, Label> > &parens_;
  PdtNShortestPathOptions opts_;
};


template <class Arc> inline
ItemId NewNShortestPath<Arc>::Prover::FindNext() {
  ItemId ret = kNoItemId;
  while (!queue_.Empty()) {
    ItemId id = Dequeue();
    StateId state = data_->chart.GetItem(id).state;
    if (state != kSuperfinal) {
      Weight rho = data_->fst->Final(state);
      if (rho != Weight::Zero())
        ProcArc(id, Arc(0, 0, rho, kSuperfinal));
      // Expand this item
      for (ArcIterator<Fst<Arc> > aiter(*data_->fst, state);
           !aiter.Done(); aiter.Next())
        ProcArc(id, aiter.Value());
    }
    if (state == final_) {
      // We have found a goal
      ret = id;
      // VLOG(0) << "Prover(" << start_ << "," << final_ << "): hit " << state << " as item " << ret << " weight " << data_->chart.GetItem(id).weight;
      break;
    }
  }
  return ret;
}

template <class Arc> inline
void NewNShortestPath<Arc>::Prover::ProcArc(ItemId id, const Arc &arc) {
  Label open_paren = data_->pdata.OpenParenId(arc.ilabel);
  // VLOG(0) << "Prover(" << start_ << "," << final_ << "): ProcArc(" << id << "," << arc.nextstate << ")" << open_paren;
  if (open_paren == kNoLabel) {
    // lexical arc
    Scan(id, arc);
  } else if (open_paren == arc.ilabel) {
    // open paren
    ItemId id1 = id;
    StateId open_dest = arc.nextstate;
    for (typename PdtParenData<Arc>::Iterator close_it =
             data_->pdata.FindClose(open_paren, open_dest);
         !close_it.Done(); close_it.Next()) {
      const FullArc<Arc> &fa = close_it.Value();
      Promise(id1, arc, fa.state, fa.arc);
    //   StateId close_src = fa.state;
    //   Promise(id1, arc, fa)
    //   ItemId id2 = pool_->GetProver(open_dest, close_src)->Head();
    //   Complete(id1, arc, id2, fa.arc);
    }
  }
}

template <class Arc> inline
void NewNShortestPath<Arc>::Prover::Scan(ItemId id, const Arc &arc) {
  Enqueue(arc.nextstate,
          Times(data_->chart.GetItem(id).weight, arc.weight),
          Parent::LexParent(id, arc));
}

template <class Arc> inline
void NewNShortestPath<Arc>::Prover::Promise(ItemId id1, const Arc &open_arc,
                                            StateId close_src, const Arc &close_arc) {
  StateId open_dest = open_arc.nextstate;
  Weight jump = data_->heuristic.Score(open_dest, close_src, Weight::One());
  Enqueue(close_arc.nextstate,
          Times(data_->chart.GetItem(id1).weight,
                Times(open_arc.weight,
                      Times(jump, close_arc.weight))),
          Parent::PromiseParent(id1, open_arc, close_src, close_arc));
}

template <class Arc> inline
void NewNShortestPath<Arc>::Prover::Complete(ItemId id1, const Arc &arc1, ItemId id2, const Arc &arc2) {
  Enqueue(arc2.nextstate,
          Times(data_->chart.GetItem(id1).weight,
                Times(arc1.weight,
                      Times(data_->chart.GetItem(id2).weight,
                            arc2.weight))),
          Parent::ParParent(id1, arc1, id2, arc2));
}

template <class Arc> inline
void NewNShortestPath<Arc>::Prover::Enqueue(StateId state, Weight weight, Parent parent) {
  Weight priority = data_->heuristic.Score(state, final_, weight);
  if (priority != Weight::Zero()) {
    ItemId id = data_->chart.AddItem(start_, state,
                                     weight, priority,
                                     parent);
    // VLOG(0) << "Prover(" << start_ << "," << final_ << "): enqueue " << state << " as item " << id << " via item " << parent.item1 << " + item " << parent.item2 << " weight " << weight << " priority " << priority;
    queue_.Insert(id);
    ++data_->n_enqueued_;
  }
}

template <class Arc> inline
ItemId NewNShortestPath<Arc>::Prover::Dequeue() {
  ItemId id = queue_.Pop();
  // VLOG(0) << "Prover(" << start_ << "," << final_ << "): dequeue " << data_->chart.GetItem(id).state << " as item " << id << " weight " << data_->chart.GetItem(id).weight
  //         << " priority " << data_->chart.GetItem(id).priority;
  Parent parent = data_->chart.GetItem(id).parent;
  if (parent.IsPromiseParent()) {
    // This is a promise of proof; now actually prove it.
    // VLOG(0) << "Prover(" << start_ << "," << final_ << "): forcing promise via " << parent.arc1.nextstate << "~>" << parent.src2;
    ItemId id2 = pool_->GetProver(parent.arc1.nextstate, parent.src2)->Head();
    // VLOG(0) << "Prover(" << start_ << "," << final_ << "): promise forced with item " << id2;
    data_->chart.ForcePromise(id, id2);
    parent = data_->chart.GetItem(id).parent;
  }

  if (parent.IsParParent()) {
    ItemId id2 = parent.item2;
    const Item &item2 = data_->chart.GetItem(id2);
    StateId start2 = item2.start, state2 = item2.state;
    ItemId next2 = item2.next;
    // VLOG(0) << "LALALA " << id2 << " " << next2 << " " << start2 << "~>" << state2;
    if (next2 == id2)              // last item proved; not necessarily last item of all
      next2 = pool_->GetProver(start2, state2)->Advance(id2);
    if (next2 != kNoItemId) {
      // VLOG(0) << "Prover(" << start_ << "," << final_ << "): dequeue triggered " << start2 << "~>" << state2 << " complete item " << next2;
      Complete(parent.item1, parent.arc1, next2, parent.arc2);
    }
  }
  ++data_->n_dequeued_;
  // if (n_dequeued_ % 10000 == 0)
  //   VLOG(0) << "Prover(" << start_ << "," << final_ << "): dequeued " << n_dequeued_;
  return id;
}

} // namespace pdt

template <class Arc, template <class> class Heuristic>
size_t NShortestPath(const Fst<Arc> &ifst,
                     const vector<pair<typename Arc::Label,
                     typename Arc::Label> > &parens,
                     MutableFst<Arc> *ofst,
                     const PdtNShortestPathOptions &opts) {
  pdt::PdtNShortestPath<Arc, Heuristic> pnsp(ifst, parens, opts);
  return pnsp.NShortestPath(ofst);
}

template <class Arc>
size_t NShortestPath(const Fst<Arc> &ifst,
                     const vector<pair<typename Arc::Label,
                     typename Arc::Label> > &parens,
                     MutableFst<Arc> *ofst,
                     size_t n) {
  return NShortestPath<Arc, pdt::OutsideHeuristic>(ifst, parens, ofst, PdtNShortestPathOptions(n));
}

template <class Arc>
size_t NShortestPath(const Fst<Arc> &ifst,
                     const vector<pair<typename Arc::Label, typename Arc::Label> > &parens,
                     MutableFst<Arc> *ofst,
                     size_t n, bool) {
  pdt::NewNShortestPath<Arc> solver(ifst,parens, PdtNShortestPathOptions(n));
  return solver.NShortestPath(ofst);
}

} // namespace fst

#endif  // FST_EXTENSIONS_PDT_N_SHORTEST_PATH_H__
