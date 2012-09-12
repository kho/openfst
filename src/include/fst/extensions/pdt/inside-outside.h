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

namespace fst {
namespace pdt {
// A Span from start to state; used as search states
template <class Arc>
struct Span {
  typename Arc::StateId start, state;
  Span(typename Arc::StateId p, typename Arc::StateId q) :
      start(p), state(q) {}
  bool operator==(const Span<Arc> &that) const {
    return this == &that || (start == that.start && state == that.state);
  }
};
} // namespace pdt
} // namespace fst

namespace std {
namespace tr1 {
template <class Arc>
struct hash<fst::pdt::Span<Arc> > {
  size_t operator()(const fst::pdt::Span<Arc> &sp) const {
    return sp.start * 7853 ^ sp.state;
  }
};
} // namespace tr1
} // namespace std

namespace fst {
namespace pdt {
// Id to chart items
typedef int ItemId;
const ItemId kNoItemId = -1;

// A hallucinated "final" state to which every real final state
// points; then the final state weight can be represented as an arc,
// which simplifies the following algorithms. Also used in finding n
// shortest paths.
const int kSuperfinal = -2;

//
// Inside chart and inside algorithm
//

template <class Arc>
class InsideChart {
 public:
  typedef typename Arc::StateId StateId;
  typedef typename Arc::Weight Weight;
  typedef typename Arc::Label Label;

  void Clear() {
    weights_.clear();
    groups_.clear();
  }

  ItemId Find(StateId start, StateId state) const {
    typename StateStartMap::const_iterator it1 = groups_.find(state);
    if (it1 == groups_.end())
      return kNoItemId;
    typename StartMap::const_iterator it2 = it1->second.find(start);
    if (it2 == it1->second.end())
      return kNoItemId;
    return it2->second;
  }

  ItemId FindOrAdd(StateId start, StateId state) {
    ItemId id = Find(start, state);
    if (id == kNoItemId) {
      id = weights_.size();
      weights_.push_back(Weight::Zero());
      groups_[state][start] = id;
    }
    return id;
  }

  Weight InsideWeight(StateId start, StateId state) const {
    ItemId id = Find(start, state);
    if (id == kNoItemId)
      return Weight::Zero();
    else
      return InsideWeight(id);
  }

  Weight InsideWeight(ItemId id) const {
    return weights_[id];
  }

  void SetInsideWeight(ItemId id, Weight weight) {
    weights_[id] = weight;
  }

  size_t Size() const {
    return weights_.size();
  }

  size_t TimeStamp(StateId start, StateId state) const {
    return TimeStamp(Span<Arc>(start, state));
  }

  size_t TimeStamp(const Span<Arc> &sp) const {
    typename TimeStampMap::const_iterator it = time_stamps_.find(sp);
    return it != time_stamps_.end() ? it->second : 0;
  }

  void SetTimeStamp(StateId start, StateId state, size_t stamp) {
    time_stamps_[Span<Arc>(start, state)] = stamp;
  }

 private:
  typedef unordered_map<StateId, ItemId> StartMap;
  typedef unordered_map<StateId, StartMap> StateStartMap;
  typedef unordered_map<Span<Arc>, size_t> TimeStampMap;

 public:
  class StartIterator {
   public:
    StartIterator(const InsideChart<Arc> &chart, StateId state) :
        at_(), end_() {
      typename StateStartMap::const_iterator it =
          chart.groups_.find(state);
      if (it != chart.groups_.end()) {
        at_ = it->second.begin();
        end_ = it->second.end();
      }
    }

    bool Done() const {
      return at_ == end_;
    }

    void Next() {
      ++at_;
    }

    pair<StateId, ItemId> Value() const {
      return *at_;
    }

   private:
    typename StartMap::const_iterator at_, end_;
  };

 private:
  vector<Weight> weights_;
  StateStartMap groups_;
  TimeStampMap time_stamps_;
};


template <class Arc>
struct TimeStampCompare {
  TimeStampCompare(const InsideChart<Arc> &chart) : chart_(chart) {}

  bool operator() (const Span<Arc> &sp1, const Span<Arc> &sp2) {
    return chart_.TimeStamp(sp1) <= chart_.TimeStamp(sp2);
  }

 private:
  const InsideChart<Arc> &chart_;
};


template <class Arc, class Queue=FifoQueue<typename Arc::StateId> >
class InsideAlgo {
 public:
  typedef typename Arc::Label Label;
  typedef typename Arc::StateId StateId;
  typedef typename Arc::Weight Weight;

  InsideAlgo(const Fst<Arc> &ifst, const vector<pair<Label, Label> > &parens,
             PdtParenData<Arc> *pdata = NULL) :
      ifst_(ifst.Copy()),
      pdata_(pdata), my_pdata_(parens),
      chart_(NULL), queue_(NULL) {
    // If paren data is not given, use my own.
    if (pdata_ == NULL)
      pdata_ = &my_pdata_;
  }

  ~InsideAlgo() {
    delete ifst_;
  }

  void FillChart(InsideChart<Arc> *chart) {
    chart_ = chart;
    chart_->Clear();
    n_enqueued_ = 0;
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

    VLOG(0) << "Inside: enqueued: " << n_enqueued_
            << " in queue: " << enqueued_.size()
            << " chart: " << chart_->Size()
            << " score: " << chart_->InsideWeight(ifst_->Start(), kSuperfinal);

    chart_ = NULL;
  }

 private:
  void GetDistance(StateId);

  void ProcArc(StateId, StateId, ItemId, const Arc &);

  void Relax(StateId, StateId, Weight);
  void Enqueue(StateId, StateId);
  StateId Dequeue(StateId);

  void Scan(StateId, StateId, ItemId, const Arc &);
  void Complete(StateId, StateId, ItemId, const Arc &, StateId, StateId, ItemId, const Arc &);
  void TryCompleteAsItem1(StateId, StateId, ItemId, Label, const Arc &);
  // void TryCompleteAsItem2(StateId, StateId, ItemId, Label, const Arc &);

  const Fst<Arc> *ifst_;
  // my_pdata_ is not used if pdata_ is given at initialization
  PdtParenData<Arc> *pdata_, my_pdata_;
  InsideChart<Arc> *chart_;
  Queue *queue_;
  unordered_set<Span<Arc> > enqueued_;
  unordered_set<StateId> got_distance_;

  size_t n_enqueued_, n_dequeued_;
};

template <class Arc, class Queue> inline
void InsideAlgo<Arc, Queue>::GetDistance(StateId start) {
  if (got_distance_.count(start))
    return;

  // VLOG(0) << "GetDistance " << start;

  Queue q, *old_queue;
  old_queue = queue_;
  queue_ = &q;

  Relax(start, start, Weight::One());

  while (!queue_->Empty()) {
    StateId state = Dequeue(start);
    if (state != kSuperfinal) {
      ItemId item = chart_->Find(start, state);
      Weight rho = ifst_->Final(state);
      // VLOG(0) << "State " << state << " Rho " << rho;
      if (rho != Weight::Zero())
        ProcArc(start, state, item, Arc(0, 0, rho, kSuperfinal));
      for (ArcIterator<Fst<Arc > > aiter(*ifst_, state);
           !aiter.Done(); aiter.Next())
        ProcArc(start, state, item, aiter.Value());
    }
  }

  queue_ = old_queue;
  got_distance_.insert(start);
}

template <class Arc, class Queue> inline
void InsideAlgo<Arc, Queue>::ProcArc(StateId start, StateId state,
                                     ItemId item, const Arc &arc) {
  // VLOG(0) << "ProcArc " << start << "~>" << state << " " << arc.nextstate;
  Label open_paren = pdata_->OpenParenId(arc.ilabel);
  if (open_paren == kNoLabel) {     // lexical arc
    Scan(start, state, item, arc);
  } else if (open_paren == arc.ilabel) { // open paren
    GetDistance(arc.nextstate);
    // At this point all relevant closing paren is known to pdata_ and
    // all inside items from arc.nextstate is proved
    TryCompleteAsItem1(start, state, item, open_paren, arc);
  } else {               // close paren
    pdata_->ReportCloseParen(start, state, arc);
  }
}

template <class Arc, class Queue> inline
void InsideAlgo<Arc, Queue>::Enqueue(StateId start, StateId state) {
  Span<Arc> sp(start, state);
  if (enqueued_.count(sp)) {
    queue_->Update(state);
  } else {
    queue_->Enqueue(state);
    enqueued_.insert(sp);
    ++n_enqueued_;
    if (n_enqueued_ % 100000 == 0)
      VLOG(0) << "enqueued: " << n_enqueued_ << " in queue: " << enqueued_.size() << " chart: " << chart_->Size();
  }

}

template <class Arc, class Queue> inline
typename Arc::StateId InsideAlgo<Arc, Queue>::Dequeue(StateId start) {
  StateId state = queue_->Head();
  queue_->Dequeue();
  enqueued_.erase(Span<Arc>(start, state));
  ++n_dequeued_;
  chart_->SetTimeStamp(start, state, n_dequeued_);
  // VLOG(0) << "Dequeue " << start << "~>" << state;
  return state;
}

template <class Arc, class Queue> inline
void InsideAlgo<Arc, Queue>::Relax(StateId start, StateId state, Weight weight) {
  ItemId item = chart_->FindOrAdd(start, state);
  Weight chart_weight = chart_->InsideWeight(item);
  weight = Plus(chart_weight, weight);
  if (weight != chart_weight) {
    chart_->SetInsideWeight(item, weight);
    Enqueue(start, state);
  }
}

template <class Arc, class Queue> inline
void InsideAlgo<Arc, Queue>::Scan(StateId start, StateId state,
                                  ItemId item, const Arc &arc) {
  // VLOG(0) << "Scan " << start << "~>" << state << " " << arc.nextstate;
  Relax(start, arc.nextstate, Times(chart_->InsideWeight(item), arc.weight));
}

template <class Arc, class Queue> inline
void InsideAlgo<Arc, Queue>::Complete(StateId start1, StateId state1, ItemId item1, const Arc &arc1,
                                      StateId start2, StateId state2, ItemId item2, const Arc &arc2) {
  // VLOG(0) << "Complete " << start1 << "~>" << state1
  //         << " " << arc1.nextstate
  //         << " " << start2 << "~>" << state2
  //         << " " << arc2.nextstate;
  Relax(start1, arc2.nextstate,
        Times(chart_->InsideWeight(item1),
              Times(arc1.weight,
                    Times(chart_->InsideWeight(item2), arc2.weight))));
}

// Rule (C) as it, arc, ?, ?? |- (it.start, ??.nextstate)
template <class Arc, class Queue> inline
void InsideAlgo<Arc, Queue>::TryCompleteAsItem1(StateId start1, StateId state1, ItemId item1,
                                                Label open_paren, const Arc &arc1) {
  // VLOG(0) << "TryCompleteAsItem1 " << start1 << "~>" << state1 << " " << arc1.nextstate;
  StateId open_dest = arc1.nextstate;
  for (typename PdtParenData<Arc>::Iterator close_it = pdata_->FindClose(open_paren, open_dest);
       !close_it.Done(); close_it.Next()) {
    const FullArc<Arc> &fa = close_it.Value();
    StateId close_src = fa.state;
    const Arc &arc2 = fa.arc;
    ItemId item2 = chart_->Find(open_dest, close_src);
    Complete(start1, state1, item1, arc1, open_dest, close_src, item2, arc2);
  }
}

// // Rule (C) as ?, ??, it, arc |- (?.start, arc.nextstate)
// template <class Arc, class Queue> inline
// void InsideAlgo<Arc, Queue>::TryCompleteAsItem2(StateId start2, StateId state2, ItemId item2,
//                         Label open_paren, const Arc &arc2) {
//  StateId close_src = state2;
//  for (typename PdtParenData<Arc>::Iterator open_it = pdata_->FindOpen(open_paren, close_src);
//    !open_it.Done(); open_it.Next()) {
//   const typename PdtParenData<Arc>::FullArc<Arc> &fa = open_it.Value();

//   if (fa.arc.nextstate != start2)
//    continue;

//   StateId open_src = fa.state;
//   const Arc &arc1 = fa.arc;
//   bool useful = false;

//   for (typename InsideChart<Arc>::StartIterator start_it(*chart_, open_src);
//     !start_it.Done(); start_it.Next()) {
//    useful = true;
//    const pair<StateId, ItemId> &p = start_it.Value();
//    StateId start1 = p.first;
//    ItemId item1 = p.second;
//    Complete(start1, open_src, item1, arc1, start2, state2, item2, arc2);
//   }

//   if (useful)
//    pdata_->ReportUseful(open_src, arc1, close_src, arc2);
//  }
// }

//
// Outside
//

template <class Arc>
class OutsideChart {
 public:
  typedef typename Arc::StateId StateId;
  typedef typename Arc::Label Label;
  typedef pair<typename Arc::Weight, typename Arc::Weight> Weight;

  void Clear() {
    weights_.clear();
    spans_.clear();
  }

  size_t Size() const {
    return weights_.size();
  }

  ItemId Find(StateId start, StateId state) const {
    typename SpanMap::const_iterator it = spans_.find(Span<Arc>(start, state));
    if (it == spans_.end())
      return kNoItemId;
    else
      return it->second;
  }

  ItemId FindOrAdd(StateId start, StateId state) {
    ItemId id = Find(start, state);
    if (id == kNoItemId) {
      id = weights_.size();
      weights_.push_back(Weight(Arc::Weight::Zero(), Arc::Weight::Zero()));
      spans_[Span<Arc>(start, state)] = id;
    }
    return id;
  }

  Weight OutsideWeight(StateId start, StateId state) const {
    ItemId id = Find(start, state);
    if (id == kNoItemId)
      return Weight(Arc::Weight::Zero(), Arc::Weight::Zero());
    else
      return OutsideWeight(id);
  }

  Weight OutsideWeight(ItemId id) const {
    return weights_[id];
  }

  void SetOutsideWeight(ItemId id, typename Arc::Weight left, typename Arc::Weight right) {
    weights_[id] = make_pair(left, right);
  }

 private:
  typedef unordered_map<Span<Arc>, ItemId> SpanMap;
  vector<Weight> weights_;
  SpanMap spans_;
};

template <class Arc>
class OutsideAlgo {
 public:
  typedef typename Arc::StateId StateId;
  typedef typename Arc::Weight Weight;
  typedef typename Arc::Label Label;

  OutsideAlgo(const Fst<Arc> &ifst, const vector<pair<Label, Label> > &parens,
              PdtParenData<Arc> *pdata = NULL) :
      ifst_(ifst.Copy()), parens_(parens),
      pdata_(pdata), my_pdata_(parens),
      out_chart_(NULL), in_chart_(NULL), queue_(NULL) {
    if (pdata_ == NULL)
      pdata_ = &my_pdata_;
  }

  ~OutsideAlgo() {
    delete ifst_;
  }

  void FillChart(OutsideChart<Arc> *out_chart, InsideChart<Arc> *in_chart = NULL) {
    out_chart_ = out_chart;
    out_chart_->Clear();
    n_enqueued_ = 0;

    if (ifst_->Start() == kNoStateId)
      return;

    InsideChart<Arc> local_in_chart;
    if (in_chart) {
      in_chart_ = in_chart;
    } else {
      in_chart_ = &local_in_chart;
      InsideAlgo<Arc>(*ifst_, parens_, pdata_).FillChart(in_chart_);
    }

    BuildReverseArcIndex();

    TimeStampCompare<Arc> comp(*in_chart_);
    Queue q(comp);
    queue_ = &q;

    Relax(ifst_->Start(), kSuperfinal, Weight::One(), Weight::One());

    while (!q.Empty()) {
      Span<Arc> sp = Dequeue();
      ItemId item = out_chart_->Find(sp.start, sp.state);
      for (typename ArcIndex::const_iterator it = arcs_.find(sp.state);
           it != arcs_.end() && it->first == sp.state; ++it) {
        const FullArc<Arc> &fa = it->second;
        ProcArc(sp.start, sp.state, item, fa);
      }
    }

    VLOG(0) << "Outside: enqueued: " << n_enqueued_
            << " in queue: " << enqueued_.size()
            << " chart: " << out_chart_->Size();

    in_chart_ = NULL;
    out_chart_ = NULL;
    queue_ = NULL;
  }

 private:
  typedef unordered_multimap<StateId, FullArc<Arc> > ArcIndex;
  typedef Heap<Span<Arc>, TimeStampCompare<Arc>, true> Queue;

  void BuildReverseArcIndex();

  void ProcArc(StateId, StateId, ItemId, const FullArc<Arc> &);

  void Relax(StateId, StateId, Weight, Weight);
  void Back(StateId, StateId, ItemId, const FullArc<Arc> &);
  void Down(StateId, StateId, ItemId, const FullArc<Arc> &, Label);

  void Enqueue(StateId, StateId);
  Span<Arc> Dequeue();

  const Fst<Arc> *ifst_;
  const vector<pair<Label, Label> > &parens_;
  PdtParenData<Arc> *pdata_, my_pdata_;
  OutsideChart<Arc> *out_chart_;
  InsideChart<Arc> *in_chart_;
  Queue *queue_;
  ArcIndex arcs_;
  unordered_set<Span<Arc> > enqueued_;
  size_t n_enqueued_;
};

template <class Arc> inline
void OutsideAlgo<Arc>::BuildReverseArcIndex() {
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

template <class Arc> inline
void OutsideAlgo<Arc>::ProcArc(StateId start, StateId state, ItemId item, const FullArc<Arc> &fa) {
  Label open_paren = pdata_->OpenParenId(fa.arc.ilabel);
  if (open_paren == kNoLabel)
    Back(start, state, item, fa);
  else if (open_paren != fa.arc.ilabel)
    Down(start, state, item, fa, open_paren);
}

template <class Arc> inline
void OutsideAlgo<Arc>::Relax(StateId start, StateId state, Weight left, Weight right) {
  ItemId item = out_chart_->FindOrAdd(start, state);
  pair<Weight, Weight> chart_weight = out_chart_->OutsideWeight(item);
  Weight old_product = Times(chart_weight.first, chart_weight.second),
      new_product = Times(left, right);
  if (Plus(new_product, old_product) != old_product) {
    out_chart_->SetOutsideWeight(item, left, right);
    Enqueue(start, state);
  }
}

template <class Arc> inline
void OutsideAlgo<Arc>::Back(StateId start, StateId state, ItemId item, const FullArc<Arc> &fa) {
  StateId q1 = start, q2 = fa.state;
  ItemId id = in_chart_->Find(q1, q2);
  const pair<Weight, Weight> &outter = out_chart_->OutsideWeight(item);
  if (id != kNoItemId)
    Relax(q1, q2,
          outter.first,
          Times(fa.arc.weight, outter.second));
}

template <class Arc> inline
void OutsideAlgo<Arc>::Down(StateId start, StateId state, ItemId item, const FullArc<Arc> &close_fa, Label open_paren) {
  StateId q1 = start, q4 = close_fa.state;
  const pair<Weight, Weight> &outter = out_chart_->OutsideWeight(item);

  for (typename PdtParenData<Arc>::Iterator it = pdata_->FindOpen(open_paren, q4);
       !it.Done(); it.Next()) {
    const FullArc<Arc> &open_fa = it.Value();
    StateId q2 = open_fa.state, q3 = open_fa.arc.nextstate;
    ItemId id1 = in_chart_->Find(q1, q2),
        id2 = in_chart_->Find(q3, q4);

    if (id1 != kNoItemId && id2 != kNoItemId) {
      Weight weight1 = in_chart_->InsideWeight(id1),
          weight2 = in_chart_->InsideWeight(id2);
      Relax(q1, q2,
            outter.first,
            Times(open_fa.arc.weight,
                  Times(weight2,
                        Times(close_fa.arc.weight, outter.second))));
      Relax(q3, q4,
            Times(outter.first, Times(weight1, open_fa.arc.weight)),
            Times(close_fa.arc.weight, outter.second));
    }
  }
}

template <class Arc> inline
void OutsideAlgo<Arc>::Enqueue(StateId start, StateId state) {
  Span<Arc> sp(start, state);
  if (!enqueued_.count(sp)) {
    queue_->Insert(sp);
    enqueued_.insert(sp);
    ++n_enqueued_;
    if (n_enqueued_ % 100000 == 0)
      VLOG(0) << "enqueued: " << n_enqueued_ << " in queue: " << enqueued_.size() << " chart: " << out_chart_->Size();
  }
}

template <class Arc> inline
Span<Arc> OutsideAlgo<Arc>::Dequeue() {
  Span<Arc> sp = queue_->Pop();
  enqueued_.erase(sp);
  return sp;
}

} // namespace pdt
} // namespace fst

#endif  // FST_EXTENSIONS_PDT_INSIDE_OUTSIDE_H__
