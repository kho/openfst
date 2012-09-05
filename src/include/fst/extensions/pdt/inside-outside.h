// outside.h

// Author: wuke@cs.umd.edu (Wu, Ke)
//
// \file
// Functions to compute outside weights of a PDT.

// For two states p and q, where p is either a start state or has an
// incoming open paren arc, we can define the inside and outside
// weights similar to those in parsing in the following way:

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
// Weight::Zero().

#ifndef FST_EXTENSIONS_PDT_INSIDE_OUTSIDE_H__
#define FST_EXTENSIONS_PDT_INSIDE_OUTSIDE_H__

#include <fst/extensions/pdt/paren-data.h>
#include <fst/queue.h>

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
// id to chart items
typedef int ItemId;
const ItemId kNoItemId = -1;
const int kSuperfinal = -2;

//
// Inside
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

 private:
  typedef unordered_map<StateId, ItemId> StartMap;
  typedef unordered_map<StateId, StartMap> StateStartMap;

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
};


template <class Arc, class Queue=FifoQueue<Span<Arc> > >
class InsideAlgo {
 public:
  typedef typename Arc::Label Label;
  typedef typename Arc::StateId StateId;
  typedef typename Arc::Weight Weight;

  InsideAlgo(const Fst<Arc> &ifst, const vector<pair<Label, Label> > &parens,
            PdtParenData<Arc> *pdata = NULL) :
      ifst_(ifst.Copy()),
      pdata_(pdata), my_pdata_(ifst, parens),
      chart_(NULL), queue_(NULL) {
    // If paren data is not given, use my own.
    if (pdata_ == NULL) {
      pdata_ = &my_pdata_;
      pdata_->Init();
    }
  }

  ~InsideAlgo() {
    delete ifst_;
  }

  void FillChart(InsideChart<Arc> *chart) {
    chart_ = chart;
    chart_->Clear();

    // Other functions can assume the fst has at least one state.
    if (ifst_->Start() == kNoStateId)
      return;

    Queue q;
    queue_ = &q;

    EnqueueAxioms();

    while (!q.Empty()) {
      Span<Arc> sp = Dequeue();
      if (sp.state == kSuperfinal) // no out-going arcs; no need to expand
        continue;
      // The item is guanranteed to be in chart since an enqueued item
      // is either an axiom (see EnqueueAxioms()) or enqueued in
      // Relax().
      ItemId item = chart_->Find(sp.start, sp.state);
      Weight rho = ifst_->Final(sp.state);
      // If `sp.state' is a final state, hallucinate a pseudo-arc to
      // the superfinal.
      if (rho != Weight::Zero())
        ProcArc(sp.start, sp.state, item, Arc(0, 0, rho, kSuperfinal));
      // Expand real out-going arcs
      for (ArcIterator<Fst<Arc> > aiter(*ifst_, sp.state); !aiter.Done(); aiter.Next())
        ProcArc(sp.start, sp.state, item, aiter.Value());
    }

    // At this point all reachable paren pairs have been visited thus
    // reported.
    pdata_->ClearNaive();

    chart_ = NULL;
    queue_ = NULL;
  }

 private:
  void EnqueueAxioms();
  void ProcArc(StateId, StateId, ItemId, const Arc &);

  void Relax(StateId, StateId, Weight);
  void Enqueue(StateId, StateId);
  Span<Arc> Dequeue();

  void Scan(StateId, StateId, ItemId, const Arc &);
  void Complete(StateId, StateId, ItemId, const Arc &, StateId, StateId, ItemId, const Arc &);
  void TryCompleteAsItem1(StateId, StateId, ItemId, Label, const Arc &);
  void TryCompleteAsItem2(StateId, StateId, ItemId, Label, const Arc &);

  const Fst<Arc> *ifst_;
  // my_pdata_ is not used if pdata_ is given at initialization
  PdtParenData<Arc> *pdata_, my_pdata_;
  InsideChart<Arc> *chart_;
  Queue *queue_;
  unordered_set<Span<Arc> > enqueued_;
};

template <class Arc, class Queue>
void InsideAlgo<Arc, Queue>::EnqueueAxioms() {
  typedef unordered_set<StateId> StateSet;
  StateSet axioms;
  axioms.insert(ifst_->Start());
  for (StateIterator<Fst<Arc> > siter(*ifst_); !siter.Done(); siter.Next()) {
    for (ArcIterator<Fst<Arc> > aiter(*ifst_, siter.Value()); !aiter.Done(); aiter.Next()) {
      const Arc &arc = aiter.Value();
      Label open_label = pdata_->OpenParenId(arc.ilabel);
      if (open_label == arc.ilabel) // open paren
        axioms.insert(arc.nextstate);
    }
  }
  for (typename StateSet::const_iterator i = axioms.begin(); i != axioms.end(); ++i)
    Relax(*i, *i, Weight::One());
}

template <class Arc, class Queue> inline
void InsideAlgo<Arc, Queue>::ProcArc(StateId start, StateId state,
                                     ItemId item, const Arc &arc) {
  Label open_paren = pdata_->OpenParenId(arc.ilabel);
  if (open_paren == kNoLabel)           // lexical arc
    Scan(start, state, item, arc);
  else if (open_paren == arc.ilabel)    // open paren
    TryCompleteAsItem1(start, state, item, open_paren, arc);
  else                                  // close paren
    TryCompleteAsItem2(start, state, item, open_paren, arc);
}

template <class Arc, class Queue> inline
void InsideAlgo<Arc, Queue>::Enqueue(StateId start, StateId state) {
  Span<Arc> sp(start, state);
  if (enqueued_.count(sp)) {
    queue_->Update(sp);
  } else {
    queue_->Enqueue(sp);
    enqueued_.insert(sp);
  }
}

template <class Arc, class Queue> inline
Span<Arc> InsideAlgo<Arc, Queue>::Dequeue() {
  Span<Arc> sp = queue_->Head();
  queue_->Dequeue();
  enqueued_.erase(sp);
  return sp;
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
  Relax(start, arc.nextstate, Times(chart_->InsideWeight(item), arc.weight));
}

template <class Arc, class Queue> inline
void InsideAlgo<Arc, Queue>::Complete(StateId start1, StateId state1, ItemId item1, const Arc &arc1,
                                      StateId start2, StateId state2, ItemId item2, const Arc &arc2) {
  Relax(start1, arc2.nextstate,
        Times(chart_->InsideWeight(item1),
              Times(arc1.weight,
                    Times(chart_->InsideWeight(item2), arc2.weight))));
}

// Rule (C) as it, arc, ?, ?? |- (it.start, ??.nextstate)
template <class Arc, class Queue> inline
void InsideAlgo<Arc, Queue>::TryCompleteAsItem1(StateId start1, StateId state1, ItemId item1,
                                                Label open_paren, const Arc &arc1) {
  StateId open_src = state1, open_dest = arc1.nextstate;
  for (typename PdtParenData<Arc>::Iterator close_it = pdata_->FindClose(open_paren, open_dest);
       !close_it.Done(); close_it.Next()) {
    const typename PdtParenData<Arc>::FullArc &fa = close_it.Value();
    StateId close_src = fa.state;
    const Arc &arc2 = fa.arc;
    ItemId item2 = chart_->Find(open_dest, close_src);
    if (item2 != kNoItemId) {
      pdata_->ReportUseful(open_src, arc1, close_src, arc2);
      Complete(start1, state1, item1, arc2, open_dest, close_src, item2, arc2);
    }
  }
}

// Rule (C) as ?, ??, it, arc |- (?.start, arc.nextstate)
template <class Arc, class Queue> inline
void InsideAlgo<Arc, Queue>::TryCompleteAsItem2(StateId start2, StateId state2, ItemId item2,
                                                Label open_paren, const Arc &arc2) {
  StateId close_src = state2;
  for (typename PdtParenData<Arc>::Iterator open_it = pdata_->FindOpen(open_paren, close_src);
       !open_it.Done(); open_it.Next()) {
    const typename PdtParenData<Arc>::FullArc &fa = open_it.Value();
    StateId open_src = fa.state;
    const Arc &arc1 = fa.arc;
    bool useful = false;

    for (typename InsideChart<Arc>::StartIterator start_it(*chart_, open_src);
         !start_it.Done(); start_it.Next()) {
      useful = true;
      const pair<StateId, ItemId> &p = start_it.Value();
      StateId start1 = p.first;
      ItemId item1 = p.second;
      Complete(start1, open_src, item1, arc1, start2, state2, item2, arc2);
    }

    if (useful)
      pdata_->ReportUseful(open_src, arc1, close_src, arc2);
  }
}

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

template <class Arc, class Queue=FifoQueue<Span<Arc> > >
class OutsideAlgo {
 public:
  typedef typename Arc::StateId StateId;
  typedef typename Arc::Weight Weight;
  typedef typename Arc::Label Label;

  OutsideAlgo(const Fst<Arc> &ifst, const vector<pair<Label, Label> > &parens,
              PdtParenData<Arc> *pdata = NULL) :
      ifst_(ifst.Copy()), parens_(parens),
      pdata_(pdata), my_pdata_(ifst, parens),
      out_chart_(NULL), in_chart_(NULL), queue_(NULL) {
    if (pdata_ == NULL) {
      pdata_ = &my_pdata_;
      pdata_->Init();
    }
  }

  ~OutsideAlgo() {
    delete ifst_;
  }

  void FillChart(OutsideChart<Arc> *out_chart, InsideChart<Arc> *in_chart = NULL) {
    out_chart_ = out_chart;
    out_chart_->Clear();

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

    Queue q;
    queue_ = &q;

    EnqueueAxioms();

    while (!q.Empty()) {
      Span<Arc> sp = Dequeue();
      ItemId item = out_chart_->Find(sp.start, sp.state);
      for (typename ArcIndex::const_iterator it = arcs_.find(sp.state);
           it != arcs_.end() && it->first == sp.state; ++it) {
        const FullArc &fa = it->second;
        ProcArc(sp.start, sp.state, item, fa);
      }
    }

    in_chart_ = NULL;
    out_chart_ = NULL;
    queue_ = NULL;
  }

 private:
  typedef typename PdtParenData<Arc>::FullArc FullArc;
  typedef unordered_multimap<StateId, FullArc> ArcIndex;

  void BuildReverseArcIndex();
  void EnqueueAxioms();
  void ProcArc(StateId, StateId, ItemId, const FullArc &);

  void Relax(StateId, StateId, Weight, Weight);
  void Back(StateId, StateId, ItemId, const FullArc &);
  void Down(StateId, StateId, ItemId, const FullArc &, Label);

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
};

template <class Arc, class Queue> inline
void OutsideAlgo<Arc, Queue>::BuildReverseArcIndex() {
  for (StateIterator<Fst<Arc> > siter(*ifst_); !siter.Done(); siter.Next()) {
    StateId s = siter.Value();
    Weight rho = ifst_->Final(s);
    // Hallucinate the pseudo-arc
    if (rho != Weight::Zero())
      arcs_.insert(make_pair(kSuperfinal, FullArc(s, Arc(0, 0, rho, kSuperfinal))));
    for (ArcIterator<Fst<Arc> > aiter(*ifst_, s); !aiter.Done(); aiter.Next()) {
      const Arc &arc = aiter.Value();
      arcs_.insert(make_pair(arc.nextstate, FullArc(s, arc)));
    }
  }
}

template <class Arc, class Queue> inline
void OutsideAlgo<Arc, Queue>::EnqueueAxioms() {
  Relax(ifst_->Start(), kSuperfinal, Weight::One(), Weight::One());
}

template <class Arc, class Queue> inline
void OutsideAlgo<Arc, Queue>::ProcArc(StateId start, StateId state, ItemId item, const FullArc &fa) {
  Label open_paren = pdata_->OpenParenId(fa.arc.ilabel);
  if (open_paren == kNoLabel)
    Back(start, state, item, fa);
  else if (open_paren != fa.arc.ilabel)
    Down(start, state, item, fa, open_paren);
}

template <class Arc, class Queue> inline
void OutsideAlgo<Arc, Queue>::Relax(StateId start, StateId state, Weight left, Weight right) {
  ItemId item = out_chart_->FindOrAdd(start, state);
  pair<Weight, Weight> chart_weight = out_chart_->OutsideWeight(item);
  Weight old_product = Times(chart_weight.first, chart_weight.second),
      new_product = Times(left, right);
  if (Plus(new_product, old_product) != old_product) {
    out_chart_->SetOutsideWeight(item, left, right);
    Enqueue(start, state);
  }
}

template <class Arc, class Queue> inline
void OutsideAlgo<Arc, Queue>::Back(StateId start, StateId state, ItemId item, const FullArc &fa) {
  StateId q1 = start, q2 = fa.state;
  ItemId id = in_chart_->Find(q1, q2);
  const pair<Weight, Weight> &outter = out_chart_->OutsideWeight(item);
  if (id != kNoItemId)
    Relax(q1, q2,
          outter.first,
          Times(fa.arc.weight, outter.second));
}

template <class Arc, class Queue> inline
void OutsideAlgo<Arc, Queue>::Down(StateId start, StateId state, ItemId item, const FullArc &close_fa, Label open_paren) {
  StateId q1 = start, q4 = close_fa.state;
  const pair<Weight, Weight> &outter = out_chart_->OutsideWeight(item);

  for (typename PdtParenData<Arc>::Iterator it = pdata_->FindOpen(open_paren, q4);
       !it.Done(); it.Next()) {
    const FullArc &open_fa = it.Value();
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

template <class Arc, class Queue> inline
void OutsideAlgo<Arc, Queue>::Enqueue(StateId start, StateId state) {
  Span<Arc> sp(start, state);
  if (enqueued_.count(sp)) {
    queue_->Update(sp);
  } else {
    queue_->Enqueue(sp);
    enqueued_.insert(sp);
  }
}

template <class Arc, class Queue> inline
Span<Arc> OutsideAlgo<Arc, Queue>::Dequeue() {
  Span<Arc> sp = queue_->Head();
  queue_->Dequeue();
  enqueued_.erase(sp);
  return sp;
}

} // namespace pdt
} // namespace fst

#endif  // FST_EXTENSIONS_PDT_INSIDE_OUTSIDE_H__
