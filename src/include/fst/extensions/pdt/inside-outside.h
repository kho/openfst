// outside.h

// Author: wuke@cs.umd.edu (Wu, Ke)
//
// \file
// Functions to compute outside weights of a PDT.

// For two states p and q, where p is either a start state or has an
// incoming open paren arc, the outside weight of (p, q) is defined as
// a pair of weights (w1, w2) such that for any balanced path from p
// to q with weight w, w1 x w x w2 is the shortest distance from start
// to final via the path. For this to be well-defined, the weight has
// to satisfy the following condition: for any w, w1, w2, w1', w2', w1
// x w2 <= w1' x w2' implies w1 x w x 2 <= w1' x w x w2'. A common
// sufficient condition is the semiring being commutative.

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

template <class Arc>
struct SearchState {
  typename Arc::StateId start, state;
  SearchState(typename Arc::StateId p, typename Arc::StateId q) :
      start(p), state(q) {}
  bool operator==(const SearchState &that) {
    return this == &that || (start == that.start && state == that.state);
  }

  struct Hash {
    size_t operator()(const SearchState<Arc> &sst) {
      return sst.start * 7853 + sst.state;
    }
  };
};

template <class Arc>
struct PdtInsideItem {
  typename Arc::StateId start, state;
  typename Arc::Weight weight;

  PdtInsideItem(typename Arc::StateId p,
                typename Arc::StateId q,
                const typename Arc::Weight &w) :
      start(p), state(q), weight(w) {}
};

typedef int ItemId;
const ItemId kNoItemId = -1;
const int kSuperfinal = -2;

template <class Arc>
class InsideChart {
 public:
  typedef typename Arc::StateId StateId;
  typedef typename Arc::Weight Weight;
  typedef typename Arc::Label Label;
  typedef PdtInsideItem<Arc> Item;

  void Clear() {
    items_.clear();
    groups_.clear();
  }

  ItemId FindItem(StateId start, StateId state) const {
    typename StateStartMap::const_iterator it1 = groups_.find(state);
    if (it1 == groups_.end())
      return kNoItemId;
    typename StartMap::const_iterator it2 = it1->second.find(start);
    if (it2 == it1->second.end())
      return kNoItemId;
    return it2->second;
  }

  Item &FindOrAddItem(StateId start, StateId state) {
    ItemId id = FindItem(start, state);
    if (id == kNoItemId) {
      id = items_.size();
      items_.push_back(PdtInsideItem<Arc>(start, state, Weight::Zero()));
      groups_[state][start] = id;
    }
    return items_[id];
  }

  Item &GetItem(ItemId id) {
    return items_[id];
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
        at_ = it->first;
        end_ = it->second;
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
  vector<Item> items_;
  StateStartMap groups_;
};


template <class Arc, class Queue=FifoQueue<SearchState<Arc> > >
class PdtInside {
 public:
  typedef typename Arc::Label Label;
  typedef typename Arc::StateId StateId;
  typedef typename Arc::Weight Weight;

  PdtInside(const Fst<Arc> &ifst, const vector<pair<Label, Label> > &parens,
            PdtParenData<Arc> *pdata = NULL) :
      ifst_(ifst.Copy()),
      pdata_(pdata), my_pdata_(ifst, parens),
      chart_(NULL), queue_(NULL) {
    if (pdata_ == NULL) {
      pdata_ = &my_pdata_;
      pdata_->Init();
    }
  }

  ~PdtInside() {
    delete ifst_;
  }

  void FillChart(InsideChart<Arc> *chart) {
    chart_ = chart;
    chart_->Clear();

    if (ifst_->Start() == kNoStateId)
      return;

    Queue q;
    queue_ = &q;

    EnqueueAxioms();

    while (!q.Empty()) {
      SState sst = q.Pop();
      Item &chart_item = chart_->FindOrAddItem(sst.start, sst.state);
      if (sst.state == kSuperfinal) // no out-going arcs; no need to expand
        continue;
      Weight rho = ifst_->Final(sst.state);
      // If `sst.state' is a final state, hallucinate a pseudo-arc
      // to the superfinal
      if (rho != Weight::Zero())
        ProcArc(chart_item, Arc(0, 0, rho, kSuperfinal));
      for (ArcIterator<Fst<Arc> > aiter(*ifst_, sst.state); !aiter.Done(); aiter.Next())
        ProcArc(chart_item, aiter.Value());
    }

    pdata_->ClearNaive();
  }

 private:
  typedef SearchState<Arc> SState;
  typedef typename InsideChart<Arc>::Item Item;

  void Enqueue(StateId, StateId);
  void EnqueueAxioms();
  void ProcArc(const Item &, const Arc &);
  void Relax(StateId, StateId, const Weight &);
  void Scan(const Item &, const Arc &);
  void Complete(const Item &, const Arc &, const Item &, const Arc &);
  void TryCompleteAsItem1(const Item &, Label, const Arc &);
  void TryCompleteAsItem2(const Item &, Label, const Arc &);

  const Fst<Arc> *ifst_;
  // my_pdata_ is not used if pdata_ is given at initialization
  PdtParenData<Arc> *pdata_, my_pdata_;
  InsideChart<Arc> *chart_;
  Queue *queue_;
  unordered_set<SState, typename SState::Hash> enqueued_;
};

template <class Arc, class Queue> inline
void PdtInside<Arc, Queue>::Enqueue(StateId start, StateId state) {
  SState sst(start, state);
  if (enqueued_.count(sst)) {
    queue_->Update(sst);
  } else {
    queue_->Enqueue(sst);
    enqueued_.insert(sst);
  }
}

template <class Arc, class Queue>
void PdtInside<Arc, Queue>::EnqueueAxioms() {
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
  for (typename StateSet::const_iterator i = axioms.begin(); i != axioms.end(); ++i) {
    Item &item = chart_->FindOrAddItem(*i, *i);
    item.weight = Weight::One();
    Enqueue(*i, *i);
  }
}

template <class Arc, class Queue> inline
void PdtInside<Arc, Queue>::ProcArc(const Item &item, const Arc &arc) {
  Label open_paren = pdata_->OpenParenId(arc.ilabel);
  if (open_paren == kNoLabel)           // lexical arc
    Scan(item, arc);
  else if (open_paren == arc.ilabel)    // open paren
    TryCompleteAsItem1(item, open_paren, arc);
  else                                  // close paren
    TryCompleteAsItem2(item, open_paren, arc);
}

template <class Arc, class Queue> inline
void PdtInside<Arc, Queue>::Relax(StateId start, StateId state, const Weight &weight) {
  Item &item = chart_->FindOrAddItem(start, state);
  Weight new_weight = Plus(item.weight, weight);
  if (new_weight != item.weight) {
    item.weight = new_weight;
    Enqueue(start, state);
  }
}

template <class Arc, class Queue> inline
void PdtInside<Arc, Queue>::Scan(const Item &item, const Arc &arc) {
  Relax(item.start, arc.nextstate, Times(item.weight, arc.weight));
}

template <class Arc, class Queue> inline
void PdtInside<Arc, Queue>::Complete(const Item &item1, const Arc &arc1,
                              const Item &item2, const Arc &arc2) {
  Relax(item1.start, arc2.nextstate,
        Times(item1.weight,
              Times(arc1.weight,
                    Times (item2.weight, arc2.weight))));
}

// Rule (C) as it, arc, ?, ?? |- (it.start, ??.nextstate)
template <class Arc, class Queue> inline
void PdtInside<Arc, Queue>::TryCompleteAsItem1(const Item &item1, Label open_paren, const Arc &arc1) {
  StateId open_src = item1.state, open_dest = arc1.nextstate;
  for (typename PdtParenData<Arc>::Iterator close_it = pdata_->FindClose(open_paren, open_dest);
       !close_it.Done(); close_it.Next()) {
    const typename PdtParenData<Arc>::FullArc &fa = close_it.Value();
    StateId close_src = fa.state;
    const Arc &arc2 = fa.arc;
    ItemId item2_id = chart_->FindItem(open_dest, close_src);
    if (item2_id != kNoItemId) {
      const Item &item2 = chart_->GetItem(item2_id);
      pdata_->ReportUseful(open_src, arc1, close_src, arc2);
      Complete(item1, arc2, item2, arc2);
    }
  }
}

// Rule (C) as ?, ??, it, arc |- (?.start, arc.nextstate)
template <class Arc, class Queue> inline
void PdtInside<Arc, Queue>::TryCompleteAsItem2(const Item &item2, Label open_paren, const Arc &arc2) {
  StateId close_src = item2.state;
  for (typename PdtParenData<Arc>::Iterator open_it = pdata_->FindOpen(open_paren, close_src);
       !open_it.Done(); open_it.Next()) {
    const typename PdtParenData<Arc>::FullArc &fa = open_it.Value();
    StateId open_src = fa.state;
    const Arc &arc1 = fa.arc;
    for (typename InsideChart<Arc>::StartIterator start_it(*chart_, open_src);
         !start_it.Done(); start_it.Next()) {
      const pair<StateId, ItemId> &p = start_it.Value();
      StateId start = p.first;
      const Item &item1 = chart_->GetItem(p.second);
      pdata_->ReportUseful(open_src, arc1, close_src, arc2);
      Complete(item1, arc1, item2, arc2);
    }
  }
}

} // namespace pdt
} // namespace fst

#endif  // FST_EXTENSIONS_PDT_INSIDE_OUTSIDE_H__
