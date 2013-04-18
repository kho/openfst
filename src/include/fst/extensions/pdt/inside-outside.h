// outside.h

// Author: wuke@cs.umd.edu (Wu, Ke)
//
// \file
// Functions to compute outside weights of a PDT.

// For two states p and q, where p is either a start state or has an
// incoming open paren arc (call p an axiom state), we can define the
// inside and outside weights similar to those in parsing in the
// following way:

// The inside weight of (p, q) is the shortest distance from p to q
// via any balanced path.

// The outside weight of (p, q) is a pair of weights (w1, w2) such
// that for any balanced path from p to q with weight w, w1 x w x w2
// is the shortest distance from start to final via the path. For this
// to be well-defined, the weight has to satisfy the following
// condition: for any w, w1, w2, w1', w2', w1 x w2 <= w1' x w2'
// implies w1 x w x 2 <= w1' x w x w2'. A common sufficient condition
// is the semiring being commutative.

// For states that are not the start state or does not have an
// open-paren incoming arc, these weights are assumed to be
// Weight::Zero(). Furthermore, for axiom states that can not be
// reached, we do not care about their inside or outside weights.

#ifndef FST_EXTENSIONS_PDT_INSIDE_OUTSIDE_H__
#define FST_EXTENSIONS_PDT_INSIDE_OUTSIDE_H__

#include <fst/extensions/pdt/paren-data.h>
#include <fst/queue.h>
#include <fst/heap.h>

#include <tr1/unordered_map>
using std::tr1::unordered_map;
#include <tr1/unordered_set>
using std::tr1::unordered_set;
#include <utility>
using std::pair;
#include <vector>
using std::vector;

// #include <ctime>
// using std::clock;
// using std::clock_t;
// class Timer {
//  public:
//   typedef int Id;

//   static Timer &Get(Id id) {
//     unordered_map<Id, Timer>::iterator it = pool_.find(id);
//     if (it != pool_.end()) {
//       return it->second;
//     } else {
//       return pool_.insert(make_pair(id, Timer(id))).first->second;
//     }
//   }

//   void Start() {
//     last_ = clock();
//   }

//   void Record(const string &message) {
//     clock_t stamp = clock();
//     records_.push_back(make_pair(message, stamp - last_));
//     last_ = clock();
//   }

//  private:
//   Timer(Id id) : id_(id) {}

//  public:
//   ~Timer() {
//     if (!records_.empty()) {
//       VLOG(0) << "Timer " << id_;
//       for (size_t i = 0; i < records_.size(); ++i) {
//         const pair<string, clock_t> d = records_[i];
//         VLOG(0) << d.first << " " << static_cast<double>(d.second) / CLOCKS_PER_SEC * 1000 << "ms";
//       }
//     }
//   }

//  private:
//   static unordered_map<Id, Timer> pool_;
//   Id id_;
//   clock_t last_;
//   vector<pair<string, clock_t> > records_;
// };

// unordered_map<Timer::Id, Timer> Timer::pool_;

namespace fst {
namespace pdt {
// A Span from start to state; used as search states
template <class Arc>
struct Span {
  typename Arc::StateId start, state;
  Span(typename Arc::StateId p, typename Arc::StateId q) :
      start(p), state(q) {}
  bool operator==(const Span<Arc> &that) const {
    return start == that.start && state == that.state;
  }
};
} // namespace pdt
} // namespace fst

namespace std {
namespace tr1 {
template <class Arc>
struct hash<fst::pdt::Span<Arc> > {
  size_t operator()(const fst::pdt::Span<Arc> &sp) const {
    return sp.start * 2750519 ^ sp.state;
  }
};
} // namespace tr1
} // namespace std

namespace fst {
namespace pdt {
// Id to chart items
typedef int ItemId;
const ItemId kNoItemId = -1;
// A promise to an proveable item
const ItemId kPromiseItem = -2;

// A hallucinated "final" state to which every real final state
// points; then the final state weight can be represented as an arc,
// which simplifies the following algorithms. Also used in finding n
// shortest paths.
const int kSuperfinal = -2;

template <class InWeight>
struct OutWeightOp {
  typedef pair<InWeight, InWeight> OutWeight;

  static inline OutWeight LeftTimes(OutWeight o, InWeight l) {
    o.first = Times(o.first, l);
    return o;
  }

  static inline OutWeight RightTimes(OutWeight o, InWeight r) {
    o.second = Times(r, o.second);
    return o;
  }

  static inline OutWeight LeftRightTimes(OutWeight o, InWeight l, InWeight r) {
    o.first = Times(o.first, l);
    o.second = Times(r, o.second);
    return o;
  }

  static inline InWeight MiddleTimes(OutWeight o, InWeight m) {
    return Times(o.first, Times(m, o.second));
  }

  static inline bool Compare(OutWeight a, OutWeight b) {
    InWeight aa = Times(a.first, a.second), bb = Times(b.first, b.second);
    return Plus(aa, bb) == aa;
  }

  static inline OutWeight One() {
    return make_pair(InWeight::One(), InWeight::One());
  }

  static inline OutWeight Zero() {
    return make_pair(InWeight::Zero(), InWeight::Zero());
  }
};

template <>
struct OutWeightOp<TropicalWeight> {
  typedef TropicalWeight InWeight;
  typedef TropicalWeight OutWeight;

  static inline OutWeight LeftTimes(OutWeight o, InWeight l) {
    return Times(o, l);
  }

  static inline OutWeight RightTimes(OutWeight o, InWeight r) {
    return Times(o, r);
  }

  static inline OutWeight LeftRightTimes(OutWeight o, InWeight l, InWeight r) {
    return Times(o, Times(l, r));
  }

  static inline InWeight MiddleTimes(OutWeight o, InWeight m) {
    return Times(o, m);
  }

  static inline bool Compare(OutWeight a, OutWeight b) {
    return Plus(a, b) == a;
  }

  static inline OutWeight One() {
    return InWeight::One();
  }

  static inline OutWeight Zero() {
    return InWeight::Zero();
  }
};

//
// A big chart storing both inside and outside scores
//

template <class Arc>
class InsideOutsideChart {
 public:
  typedef typename Arc::Label Label;
  typedef typename Arc::StateId StateId;
  typedef typename Arc::Weight InWeight;
  typedef typename OutWeightOp<InWeight>::OutWeight OutWeight;

  struct Item {
    Span<Arc> span;
    InWeight in_weight;
    OutWeight out_weight;
    vector<ItemId> parents;            // used in topo-sort; duplicate edges should not matter
    Item() :
        span(kNoStateId, kNoStateId),
        in_weight(InWeight::Zero()),
        out_weight(OutWeightOp<InWeight>::Zero()) {}
    Item(StateId p, StateId q) :
        span(p, q),
        in_weight(InWeight::Zero()),
        out_weight(OutWeightOp<InWeight>::Zero()) {}
  };

 public:
  void Clear() {
    items_.clear();
    span_ids_.clear();
  }

  ItemId Find(StateId start, StateId state) const {
    typename SpanIdMap::const_iterator it = span_ids_.find(Span<Arc>(start, state));
    return it == span_ids_.end() ? kNoItemId : it->second;
  }

  ItemId FindOrAdd(StateId start, StateId state) {
    ItemId id = Find(start, state);
    if (id == kNoItemId) {
      id = items_.size();
      items_.push_back(Item(start, state));
      span_ids_[Span<Arc>(start, state)] = id;
    }
    return id;
  }

  size_t Size() const {
    return items_.size();
  }

  Span<Arc> GetSpan(ItemId id) const {
    return items_[id].span;
  }

  InWeight GetInsideWeight(ItemId id) const {
    return items_[id].in_weight;
  }

  void SetInsideWeight(ItemId id, InWeight weight) {
    items_[id].in_weight = weight;
  }

  OutWeight GetOutsideWeight(ItemId id) const {
    return items_[id].out_weight;
  }

  void SetOutsideWeight(ItemId id, OutWeight weight) {
    items_[id].out_weight = weight;
  }

  void AddParent(ItemId child, ItemId parent) {
    items_[child].parents.push_back(parent);
  }

  void TopologicalSort(ItemId goal, vector<ItemId> *output) const {
    output->clear();
    vector<bool> visited(items_.size(), false);
    TopologicalSort_(goal, output, &visited);
  }

 private:
  typedef unordered_map<Span<Arc>, ItemId> SpanIdMap;

  void TopologicalSort_(ItemId id, vector<ItemId> *output, vector<bool> *visited) const {
    (*visited)[id] = true;
    for (typename vector<ItemId>::const_iterator it = items_[id].parents.begin();
         it != items_[id].parents.end(); ++it)
      if (!(*visited)[*it])
        TopologicalSort_(*it, output, visited);
    output->push_back(id);
  }

  vector<Item> items_;
  SpanIdMap span_ids_;
};


template <class Arc, template <class> class Queue = FifoQueue>
class InsideAlgo {
 public:
  typedef typename Arc::Label Label;
  typedef typename Arc::StateId StateId;
  typedef typename Arc::Weight Weight;

  InsideAlgo(const Fst<Arc> &ifst, const vector<pair<Label, Label> > &parens,
             PdtParenData<Arc> *pdata = NULL) :
      ifst_(ifst.Copy()),
      pdata_(pdata), my_pdata_(parens),
      chart_(NULL), queue_(NULL), enqueued_(NULL) {
    // If paren data is not given, use my own.
    if (pdata_ == NULL)
      pdata_ = &my_pdata_;
  }

  ~InsideAlgo() {
    delete ifst_;
  }

  void FillChart(InsideOutsideChart<Arc> *chart) {
    // Timer::Get(0).Start();
    chart_ = chart;
    chart_->Clear();
    n_dequeued_ = 0;

    // Other functions can assume the FST has at least one reachable
    // state.
    if (ifst_->Start() == kNoStateId)
      return;

    pdata_->Prepare(*ifst_);

    GetDistance(ifst_->Start());

    // At this point all reachable paren pairs have been visited thus
    // reported.
    pdata_->Finalize();

    // VLOG(0) << "Inside: expansion: " << n_dequeued_
    //         << " chart: " << chart_->Size()
    //         << " weight: " << chart_->GetInsideWeight(chart_->Find(ifst_->Start(), kSuperfinal));

    chart_ = NULL;
    // Timer::Get(0).Record("Inside");
  }

 private:
  typedef unordered_set<StateId> StateIdSet;
  void GetDistance(StateId);

  void ProcArc(StateId, StateId, ItemId, const Arc &);

  ItemId Relax(StateId, StateId, Weight); // returns the id of relaxed item
  void Enqueue(StateId);
  StateId Dequeue();

  void Scan(StateId, StateId, ItemId, const Arc &);
  void Complete(StateId, StateId, ItemId, const Arc &, StateId, StateId, ItemId, const Arc &);
  void TryCompleteAsItem1(StateId, StateId, ItemId, Label, const Arc &);

  const Fst<Arc> *ifst_;
  // my_pdata_ is not used if pdata_ is given at initialization
  PdtParenData<Arc> *pdata_, my_pdata_;
  InsideOutsideChart<Arc> *chart_;
  Queue<StateId> *queue_;
  StateIdSet *enqueued_;
  StateIdSet got_distance_;

  size_t n_dequeued_;
};

template <class Arc, template <class> class Queue> inline
void InsideAlgo<Arc, Queue>::GetDistance(StateId start) {
  if (got_distance_.count(start))
    return;

  Queue<StateId> q, *old_queue;
  old_queue = queue_;
  queue_ = &q;

  StateIdSet s, *old_enqueued;
  old_enqueued = enqueued_;
  enqueued_ = &s;

  Relax(start, start, Weight::One());

  while (!queue_->Empty()) {
    StateId state = Dequeue();
    if (state != kSuperfinal) {
      ItemId item = chart_->Find(start, state);
      Weight rho = ifst_->Final(state);
      if (rho != Weight::Zero())
        ProcArc(start, state, item, Arc(0, 0, rho, kSuperfinal));
      for (ArcIterator<Fst<Arc > > aiter(*ifst_, state);
           !aiter.Done(); aiter.Next())
        ProcArc(start, state, item, aiter.Value());
    }
  }

  enqueued_ = old_enqueued;
  queue_ = old_queue;
  got_distance_.insert(start);
}

template <class Arc, template <class> class Queue> inline
void InsideAlgo<Arc, Queue>::ProcArc(StateId start, StateId state,
                                     ItemId item, const Arc &arc) {
  Label open_paren = pdata_->OpenParenId(arc.ilabel);
  if (open_paren == kNoLabel) {     // lexical arc
    Scan(start, state, item, arc);
  } else if (open_paren == arc.ilabel) { // open paren
    GetDistance(arc.nextstate);
    // At this point all relevant closing paren is known to pdata_ and
    // all inside items from arc.nextstate is proved
    TryCompleteAsItem1(start, state, item, open_paren, arc);
  } else {               // close paren
    pdata_->ReportCloseParen(start, state, open_paren);
  }
}

template <class Arc, template <class> class Queue> inline
void InsideAlgo<Arc, Queue>::Enqueue(StateId state) {
  if (enqueued_->count(state)) {
    queue_->Update(state);
  } else {
    queue_->Enqueue(state);
    enqueued_->insert(state);
  }
}

template <class Arc, template <class> class Queue> inline
typename Arc::StateId InsideAlgo<Arc, Queue>::Dequeue() {
  StateId state = queue_->Head();
  queue_->Dequeue();
  enqueued_->erase(state);
  ++n_dequeued_;
  return state;
}

template <class Arc, template <class> class Queue> inline
ItemId InsideAlgo<Arc, Queue>::Relax(StateId start, StateId state, Weight weight) {
  ItemId item = chart_->FindOrAdd(start, state);
  Weight chart_weight = chart_->GetInsideWeight(item);
  weight = Plus(chart_weight, weight);
  if (weight != chart_weight) {
    chart_->SetInsideWeight(item, weight);
    Enqueue(state);
  }
  return item;
}

template <class Arc, template <class> class Queue> inline
void InsideAlgo<Arc, Queue>::Scan(StateId start, StateId state,
                                  ItemId item, const Arc &arc) {
  // VLOG(0) << "Scan " << start << "~>" << state << " " << arc.nextstate;
  ItemId new_item = Relax(start, arc.nextstate, Times(chart_->GetInsideWeight(item), arc.weight));
  chart_->AddParent(new_item, item);
}

template <class Arc, template <class> class Queue> inline
void InsideAlgo<Arc, Queue>::Complete(StateId start1, StateId state1, ItemId item1, const Arc &arc1,
                                      StateId start2, StateId state2, ItemId item2, const Arc &arc2) {
  // VLOG(0) << "Complete " << start1 << "~>" << state1
  //         << " " << arc1.nextstate
  //         << " " << start2 << "~>" << state2
  //         << " " << arc2.nextstate;
  ItemId new_item = Relax(start1, arc2.nextstate,
                          Times(chart_->GetInsideWeight(item1),
                                Times(arc1.weight,
                                      Times(chart_->GetInsideWeight(item2), arc2.weight))));
  chart_->AddParent(new_item, item1);
  chart_->AddParent(new_item, item2);
}

// Rule (C) as it, arc, ?, ?? |- (it.start, ??.nextstate)
template <class Arc, template <class> class Queue> inline
void InsideAlgo<Arc, Queue>::TryCompleteAsItem1(StateId start1, StateId state1, ItemId item1,
                                                Label open_paren, const Arc &arc1) {
  // VLOG(0) << "TryCompleteAsItem1 " << start1 << "~>" << state1 << " " << arc1.nextstate;
  StateId open_dest = arc1.nextstate;
  for (typename PdtParenData<Arc>::CloseIterator close_it = pdata_->FindClose(open_paren, open_dest);
       !close_it.Done(); close_it.Next()) {
    const FullArc<Arc> &fa = close_it.Value();
    StateId close_src = fa.state;
    const Arc &arc2 = fa.arc;
    ItemId item2 = chart_->Find(open_dest, close_src);
    Complete(start1, state1, item1, arc1, open_dest, close_src, item2, arc2);
  }
}


//
// Outside
//
template <class Arc, template <class> class Queue = FifoQueue>
class OutsideAlgo {
 public:
  typedef typename Arc::StateId StateId;
  typedef typename Arc::Label Label;
  typedef typename Arc::Weight InWeight;
  typedef typename OutWeightOp<InWeight>::OutWeight OutWeight;

  OutsideAlgo(const Fst<Arc> &ifst, const vector<pair<Label, Label> > &parens,
              PdtParenData<Arc> *pdata = NULL) :
      ifst_(ifst.Copy()), parens_(parens),
      pdata_(pdata), my_pdata_(parens),
      chart_(NULL), queue_(NULL) {
    if (pdata_ == NULL)
      pdata_ = &my_pdata_;
  }

  ~OutsideAlgo() {
    delete ifst_;
  }

  // chart must have been filled by InsideAlgo
  void FillChart(InsideOutsideChart<Arc> *chart) {
    // Timer::Get(0).Start();
    chart_ = chart;
    n_dequeued_ = 0;

    if (ifst_->Start() == kNoStateId)
      return;

    ItemId goal = chart_->Find(ifst_->Start(), kSuperfinal);
    if (goal == kNoItemId)              // no accepting path
      return;

    BuildReverseArcIndex();

    vector<ItemId> topo;
    chart_->TopologicalSort(goal, &topo);

    Queue<ItemId> q;                // used for re-expanding in case of cycles
    queue_ = &q;

    enqueued_.clear();
    seen_.clear();
    seen_.resize(chart_->Size(), false);

    Relax(goal, OutWeightOp<InWeight>::One());

    for (typename vector<ItemId>::const_reverse_iterator tit = topo.rbegin();
         tit != topo.rend(); ++tit) {
      ItemId item = *tit;
      seen_[item] = true;
      Expand(item);

      while (!q.Empty()) {
        item = Dequeue();
        Expand(item);
      }
    }

    VLOG(0) << "Outside: expansion: " << n_dequeued_ + topo.size()
            << " topo: " << topo.size();

    chart_ = NULL;
    queue_ = NULL;
    // Timer::Get(0).Record("Outside");
  }

 private:
  typedef unordered_multimap<StateId, FullArc<Arc> > ArcIndex;

  void BuildReverseArcIndex();

  void Expand(ItemId);
  void ProcArc(StateId, StateId, ItemId, const FullArc<Arc> &);

  void Relax(ItemId, OutWeight);
  void Back(StateId, StateId, ItemId, const FullArc<Arc> &);
  void Down(StateId, StateId, ItemId, const FullArc<Arc> &, Label);

  void Enqueue(ItemId);
  ItemId Dequeue();

  const Fst<Arc> *ifst_;
  const vector<pair<Label, Label> > &parens_;
  PdtParenData<Arc> *pdata_, my_pdata_;
  InsideOutsideChart<Arc> *chart_;
  Queue<ItemId> *queue_;
  ArcIndex arcs_;
  unordered_set<ItemId> enqueued_;
  vector<bool> seen_;
  size_t n_dequeued_;
};

template <class Arc, template <class> class Queue> inline
void OutsideAlgo<Arc, Queue>::BuildReverseArcIndex() {
  for (StateIterator<Fst<Arc> > siter(*ifst_); !siter.Done(); siter.Next()) {
    StateId s = siter.Value();
    InWeight rho = ifst_->Final(s);
    // Hallucinate the pseudo-arc
    if (rho != InWeight::Zero())
      arcs_.insert(make_pair(kSuperfinal, FullArc<Arc> (s, Arc(0, 0, rho, kSuperfinal))));
    for (ArcIterator<Fst<Arc> > aiter(*ifst_, s); !aiter.Done(); aiter.Next()) {
      const Arc &arc = aiter.Value();
      arcs_.insert(make_pair(arc.nextstate, FullArc<Arc> (s, arc)));
    }
  }
}

template <class Arc, template <class> class Queue> inline
void OutsideAlgo<Arc, Queue>::Expand(ItemId item) {
  Span<Arc> span = chart_->GetSpan(item);
  // VLOG(0) << "Expand " << span.start << "~>" << span.state << "@" << item << " " << chart_->GetOutsideWeight(item);
  for (typename ArcIndex::const_iterator it = arcs_.find(span.state);
       it != arcs_.end() && it->first == span.state; ++it) {
    const FullArc<Arc> &fa = it->second;
    ProcArc(span.start, span.state, item, fa);
  }
}

template <class Arc, template <class> class Queue> inline
void OutsideAlgo<Arc, Queue>::ProcArc(StateId start, StateId state, ItemId item, const FullArc<Arc> &fa) {
  Label open_paren = pdata_->OpenParenId(fa.arc.ilabel);
  if (open_paren == kNoLabel)
    Back(start, state, item, fa);
  else if (open_paren != fa.arc.ilabel)
    Down(start, state, item, fa, open_paren);
}

template <class Arc, template <class> class Queue> inline
void OutsideAlgo<Arc, Queue>::Back(StateId start, StateId state, ItemId outer, const FullArc<Arc> &fa) {
  ItemId inner = chart_->Find(start, fa.state);
  if (inner != kNoItemId) {
    // VLOG(0) << "Back " << start << "~>" << fa.state << " via " << start << "~>" << (fa.arc.nextstate == state ? state : 999999) << " " << fa.arc.weight;
    Relax(inner, OutWeightOp<InWeight>::RightTimes(chart_->GetOutsideWeight(outer), fa.arc.weight));
  }
}

template <class Arc, template <class> class Queue> inline
void OutsideAlgo<Arc, Queue>::Down(StateId start, StateId state, ItemId outer, const FullArc<Arc> &close_fa, Label open_paren) {
  StateId q1 = start, q4 = close_fa.state;

  for (typename PdtParenData<Arc>::OpenIterator it = pdata_->FindOpen(open_paren, q4);
       !it.Done(); it.Next()) {
    const FullArc<Arc> &open_fa = it.Value();
    StateId q2 = open_fa.state, q3 = open_fa.arc.nextstate;
    ItemId inner1 = chart_->Find(q1, q2), inner2 = chart_->Find(q3, q4);

    if (inner1 != kNoItemId && inner2 != kNoItemId) {
      InWeight weight1 = chart_->GetInsideWeight(inner1), weight2 = chart_->GetInsideWeight(inner2);

      // VLOG(0) << "Down " << q1 << "~>" << q2 << " via " << start << "~>" << state;
      // VLOG(0) << "Down " << q3 << "~>" << q4 << " via " << start << "~>" << state;

      Relax(inner1,
            OutWeightOp<InWeight>::RightTimes(chart_->GetOutsideWeight(outer),
                                              Times(open_fa.arc.weight,
                                                    Times(weight2, close_fa.arc.weight))));
      Relax(inner2,
            OutWeightOp<InWeight>::LeftRightTimes(chart_->GetOutsideWeight(outer),
                                                  Times(weight1, open_fa.arc.weight),
                                                  close_fa.arc.weight));
    }
  }
}

template <class Arc, template <class> class Queue> inline
void OutsideAlgo<Arc, Queue>::Relax(ItemId item, OutWeight weight) {
  OutWeight chart_weight = chart_->GetOutsideWeight(item);
  if (OutWeightOp<InWeight>::Compare(weight, chart_weight)) {
    chart_->SetOutsideWeight(item, weight);
    Enqueue(item);
  }
}

template <class Arc, template <class> class Queue> inline
void OutsideAlgo<Arc, Queue>::Enqueue(ItemId item) {
  // Only enqueue items that have been seen; items that haven't will
  // eventually be processed by the topological traversal in
  // FillChart().
  if (seen_[item]) {
    if (enqueued_.count(item)) {
      queue_->Update(item);
    } else {
      queue_->Enqueue(item);
      enqueued_.insert(item);
    }
  }
}

template <class Arc, template <class> class Queue> inline
ItemId OutsideAlgo<Arc, Queue>::Dequeue() {
  ItemId item = queue_->Head();
  queue_->Dequeue();
  enqueued_.erase(item);
  ++n_dequeued_;
  return item;
}


template <class Arc>
class SpanWeightChart {
 public:
  typedef typename Arc::Label Label;
  typedef typename Arc::StateId StateId;
  typedef typename Arc::Weight Weight;

 public:
  void Clear() {
    weights_.clear();
    span_ids_.clear();
  }

  ItemId Find(StateId start, StateId state) const {
    typename SpanIdMap::const_iterator it = span_ids_.find(Span<Arc>(start, state));
    return it == span_ids_.end() ? kNoItemId : it->second;
  }

  ItemId FindOrAdd(StateId start, StateId state) {
    ItemId id = Find(start, state);
    if (id == kNoItemId) {
      id = weights_.size();
      weights_.push_back(Weight::Zero());
      span_ids_[Span<Arc>(start, state)] = id;
    }
    return id;
  }

  size_t Size() const {
    return weights_.size();
  }

  Weight GetWeight(ItemId id) const {
    return weights_[id];
  }

  void SetWeight(ItemId id, Weight weight) {
    weights_[id] = weight;
  }

 private:
  typedef unordered_map<Span<Arc>, ItemId> SpanIdMap;

  vector<Weight> weights_;
  SpanIdMap span_ids_;
};

// Almost the same as InsideAlgo except that computes reverse inside weights
template <class Arc, template <class> class Queue = FifoQueue>
class ReverseInsideAlgo {
 public:
  typedef typename Arc::Label Label;
  typedef typename Arc::StateId StateId;
  typedef typename Arc::Weight Weight;

  ReverseInsideAlgo(const Fst<Arc> &ifst, const vector<pair<Label, Label> > &parens,
             PdtParenData<Arc> *pdata = NULL) :
      ifst_(ifst.Copy()),
      pdata_(pdata), my_pdata_(parens),
      chart_(NULL), queue_(NULL), enqueued_(NULL) {
    // If paren data is not given, use my own.
    if (pdata_ == NULL)
      pdata_ = &my_pdata_;
  }

  ~ReverseInsideAlgo() {
    delete ifst_;
  }

  void FillChart(SpanWeightChart<Arc> *chart) {
    // Timer::Get(0).Start();
    chart_ = chart;
    chart_->Clear();
    n_dequeued_ = 0;

    // Other functions can assume the FST has at least one reachable
    // state.
    if (ifst_->Start() == kNoStateId)
      return;

    BuildReverseArcIndex();

    pdata_->Prepare(*ifst_);

    GetDistance(kSuperfinal);

    // At this point all reachable paren pairs have been visited thus
    // reported.
    pdata_->Finalize();

    // VLOG(0) << "ReverseInside: expansion: " << n_dequeued_
    //         << " chart: " << chart_->Size()
    //         << " weight: " << chart_->GetWeight(chart_->Find(ifst_->Start(), kSuperfinal));

    chart_ = NULL;
    // Timer::Get(0).Record("ReverseInside");
  }

 private:
  typedef unordered_set<StateId> StateIdSet;
  typedef unordered_multimap<StateId, FullArc<Arc> > ArcIndex;

  void BuildReverseArcIndex();

  void GetDistance(StateId);

  void ProcArc(StateId, const Arc &, ItemId, StateId);

  void Relax(StateId, StateId, Weight); // returns the id of relaxed item
  void Enqueue(StateId);
  StateId Dequeue();

  void Scan(StateId, const Arc &, ItemId, StateId);
  void Complete(StateId, const Arc &, ItemId, const Arc &, ItemId, StateId);
  void TryComplete(StateId, const Arc &, ItemId, StateId, Label);

  const Fst<Arc> *ifst_;
  // my_pdata_ is not used if pdata_ is given at initialization
  PdtParenData<Arc> *pdata_, my_pdata_;
  SpanWeightChart<Arc> *chart_;
  Queue<StateId> *queue_;
  StateIdSet *enqueued_;
  StateIdSet got_distance_;
  ArcIndex arcs_;

  size_t n_dequeued_;
};

template <class Arc, template <class> class Queue> inline
void ReverseInsideAlgo<Arc, Queue>::BuildReverseArcIndex() {
  for (StateIterator<Fst<Arc> > siter(*ifst_); !siter.Done(); siter.Next()) {
    StateId s = siter.Value();
    Weight rho = ifst_->Final(s);
    // Hallucinate the pseudo-arc
    if (rho != Weight::Zero())
      arcs_.insert(make_pair(kSuperfinal, FullArc<Arc> (s, Arc(0, 0, rho, kSuperfinal))));
    for (ArcIterator<Fst<Arc> > aiter(*ifst_, s); !aiter.Done(); aiter.Next()) {
      const Arc &arc = aiter.Value();
      arcs_.insert(make_pair(arc.nextstate, FullArc<Arc> (s, arc)));
    }
  }
}

template <class Arc, template <class> class Queue> inline
void ReverseInsideAlgo<Arc, Queue>::GetDistance(StateId state) {
  if (got_distance_.count(state))
    return;

  Queue<StateId> q, *old_queue;
  old_queue = queue_;
  queue_ = &q;

  StateIdSet s, *old_enqueued;
  old_enqueued = enqueued_;
  enqueued_ = &s;

  Relax(state, state, Weight::One());

  while (!queue_->Empty()) {
    StateId start = Dequeue();
    ItemId item = chart_->Find(start, state);
    for (typename ArcIndex::const_iterator it = arcs_.find(start);
         it != arcs_.end() && it->first == start; ++it) {
      const FullArc<Arc> &fa = it->second;
      ProcArc(fa.state, fa.arc, item, state);
    }
  }

  enqueued_ = old_enqueued;
  queue_ = old_queue;
  got_distance_.insert(state);
}

//   ?
// @ -> @ ~> @
// s a    i  s
// t r    t  t
// a c    e  a
// r      m  t
// t         e
template <class Arc, template <class> class Queue> inline
void ReverseInsideAlgo<Arc, Queue>::ProcArc(StateId start, const Arc &arc, ItemId item, StateId state) {
  Label open_paren = pdata_->OpenParenId(arc.ilabel);
  if (open_paren == kNoLabel) {     // lexical arc
    Scan(start, arc, item, state);
  } else if (open_paren == arc.ilabel) { // open paren
    pdata_->ReportOpenParen(arc.nextstate, state, open_paren);
  } else {                              // close paren
    GetDistance(start);
    // At this point all relevant open paren is known to pdata_ and
    // all reverse inside items to start have been proved
    TryComplete(start, arc, item, state, open_paren);
  }
}

//   a
// @ -> @ ~> @
// s a    i  s
// t r    t  t
// a c    e  a
// r      m  t
// t         e
template <class Arc, template <class> class Queue> inline
void ReverseInsideAlgo<Arc, Queue>::Scan(StateId start, const Arc &arc, ItemId item, StateId state) {
  Relax(start, state, Times(arc.weight, chart_->GetWeight(item)));
}

//   (         )
// @ -> @ ~> @ -> @ ~> @
// s a    i  s a    i  s
// t r    t  t r    t  t
// a c    e  a c    e  a
// r 1    m  t 2    m  t
// t      1  e      2  e
// 1         1         2
template <class Arc, template <class> class Queue> inline
void ReverseInsideAlgo<Arc, Queue>::TryComplete(StateId state1, const Arc &arc2,
                                                ItemId item2, StateId state2,
                                                Label open_paren) {
  StateId close_src = state1;
  for (typename PdtParenData<Arc>::OpenIterator open_it = pdata_->FindOpen(open_paren, close_src);
       !open_it.Done(); open_it.Next()) {
    const FullArc<Arc> &fa = open_it.Value();
    StateId start1 = fa.state;
    const Arc &arc1 = fa.arc;
    StateId open_dest = arc1.nextstate;
    ItemId item1 = chart_->Find(open_dest, close_src);
    Complete(start1, arc1, item1, arc2, item2, state2);
  }
}

template <class Arc, template <class> class Queue> inline
void ReverseInsideAlgo<Arc, Queue>::Complete(StateId start1, const Arc &arc1, ItemId item1,
                                             const Arc &arc2, ItemId item2, StateId state2) {
  // VLOG(0) << "Complete " << start1 << "~>" << state1
  //         << " " << arc1.nextstate
  //         << " " << start2 << "~>" << state2
  //         << " " << arc2.nextstate;
  Relax(start1, state2,
        Times(arc1.weight,
              Times(chart_->GetWeight(item1),
                    Times(arc2.weight,
                          chart_->GetWeight(item2)))));
}

template <class Arc, template <class> class Queue> inline
void ReverseInsideAlgo<Arc, Queue>::Enqueue(StateId start) {
  if (enqueued_->count(start)) {
    queue_->Update(start);
  } else {
    queue_->Enqueue(start);
    enqueued_->insert(start);
  }
}

template <class Arc, template <class> class Queue> inline
typename Arc::StateId ReverseInsideAlgo<Arc, Queue>::Dequeue() {
  StateId start = queue_->Head();
  queue_->Dequeue();
  enqueued_->erase(start);
  ++n_dequeued_;
  return start;
}

template <class Arc, template <class> class Queue> inline
void ReverseInsideAlgo<Arc, Queue>::Relax(StateId start, StateId state, Weight weight) {
  ItemId item = chart_->FindOrAdd(start, state);
  Weight chart_weight = chart_->GetWeight(item);
  weight = Plus(chart_weight, weight);
  if (weight != chart_weight) {
    chart_->SetWeight(item, weight);
    Enqueue(start);
  }
}


} // namespace pdt
} // namespace fst

#endif  // FST_EXTENSIONS_PDT_INSIDE_OUTSIDE_H__
