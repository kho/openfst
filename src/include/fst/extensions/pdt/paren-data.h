// paren-data.h
//
// \file
// Data structure that provides parenthesis pairing information.

#ifndef FST_EXTENSIONS_PDT_PAREN_DATA_H__
#define FST_EXTENSIONS_PDT_PAREN_DATA_H__

#include <fst/fst.h>
#include <fst/extensions/pdt/paren.h>

#include <tr1/unordered_map>
using std::tr1::unordered_map;
using std::tr1::unordered_multimap;
#include <utility>
using std::make_pair;
using std::pair;
#include <vector>
using std::vector;

namespace fst {
namespace pdt {

// Arc and its source state
template <class Arc>
struct FullArc {
  FullArc(typename Arc::StateId s, const Arc &a): state(s), arc(a) {}
  typename Arc::StateId state;
  Arc arc;

  bool operator==(const FullArc &that) const {
    return this == &that || (state == that.state
                             && arc.nextstate == that.arc.nextstate
                             && arc.ilabel == that.arc.ilabel
                             && arc.olabel == that.arc.olabel
                             && arc.weight == that.arc.weight);
  }
};


//
// PdtParenData: provides closing/opening arcs for opening/closing
// parentheses and states; also assigns paren ids.
//
template <class Arc>
class PdtParenData {
 private:
  typedef typename Arc::Label Label;
  typedef typename Arc::StateId StateId;
  typedef typename Arc::Weight Weight;
  typedef unordered_map<Label, Label> ParenIdMap;
  typedef unordered_set<StateId> StateSet;
  typedef unordered_map<ParenState<Arc>, StateSet, typename ParenState<Arc>::Hash> ReachMap;
  typedef unordered_multimap<ParenState<Arc>, Arc, typename ParenState<Arc>::Hash> ArcMap;

 public:
  class OpenIterator {
   public:
    bool Done() const {
      return st_at_ == st_end_;
    };

    void Next() {
      ++ar_at_;
      if (ar_at_ == ar_end_) {
        ++st_at_;
        SetRange();
      }
    }

    FullArc<Arc> Value() const {
      FullArc<Arc> ret(kNoStateId, ar_at_->second);
      ret.state = ret.arc.nextstate;
      ret.arc.nextstate = *st_at_;
      return ret;
    }

   private:
    typedef typename StateSet::const_iterator StIter;
    typedef typename ArcMap::const_iterator ArIter;

    OpenIterator() :
        paren_(kNoLabel), st_at_(), st_end_(), ar_at_(), ar_end_(), open_arcs_(NULL) {
    }

    OpenIterator(Label open_paren, const StateSet &open_dests, const ArcMap &open_arcs) :
        paren_(open_paren), st_at_(open_dests.begin()), st_end_(open_dests.end()), open_arcs_(&open_arcs) {
      SetRange();
    }

    void SetRange() {
      if (Done())
        return;
      pair<ArIter, ArIter> range = open_arcs_->equal_range(ParenState<Arc>(paren_, *st_at_));
      ar_at_ = range.first;
      ar_end_ = range.second;
    }

    Label paren_;
    StIter st_at_, st_end_;
    ArIter ar_at_, ar_end_;
    const ArcMap *open_arcs_;

    template <class A> friend class PdtParenData;
  };

  class CloseIterator {
   public:
    bool Done() const {
      return st_at_ == st_end_;
    };

    void Next() {
      ++ar_at_;
      if (ar_at_ == ar_end_) {
        ++st_at_;
        SetRange();
      }
    }

    FullArc<Arc> Value() const {
      FullArc<Arc> ret(*st_at_, ar_at_->second);
      return ret;
    }

   private:
    typedef typename StateSet::const_iterator StIter;
    typedef typename ArcMap::const_iterator ArIter;

    CloseIterator() :
        paren_(kNoLabel), st_at_(), st_end_(), ar_at_(), ar_end_(), close_arcs_(NULL) {
    }

    CloseIterator(Label open_paren, const StateSet &close_srcs, const ArcMap &close_arcs) :
        paren_(open_paren), st_at_(close_srcs.begin()), st_end_(close_srcs.end()), close_arcs_(&close_arcs) {
      SetRange();
    }

    void SetRange() {
      if (Done())
        return;
      pair<ArIter, ArIter> range = close_arcs_->equal_range(ParenState<Arc>(paren_, *st_at_));
      ar_at_ = range.first;
      ar_end_ = range.second;
    }

    Label paren_;
    StIter st_at_, st_end_;
    ArIter ar_at_, ar_end_;
    const ArcMap *close_arcs_;

    template <class A> friend class PdtParenData;
  };

  // The constructor only assigns paren ids
  PdtParenData(const vector<pair<Label, Label> > &parens) :
      finalized_(false) {
    AssignParenId(parens);
  }

  // Finds the open paren of a given label; if the label is a paren,
  // its open paren label is returned; otherwise kNoLabel is
  // returned. Useful for both normalizing paren identification and
  // testing the kind of a label. Must be called after Init().
  //
  // To test if a label is
  // - An open paren, use (label != kNoLabel && OpenParenId(label) == label);
  // - A close paren, use (label != kNoLabel && OpenParenId(label) != kNoLabel && OpenParenId(label) != label);
  // - A lexical paren, use (label != kNoLabel && OpenParenId(label) == label).
  Label OpenParenId(Label l) const {
    typename ParenIdMap::const_iterator it = open_paren_.find(l);
    return it == open_paren_.end() ? kNoLabel : it->second;
  }

  // Finds all open/close paren arcs
  void Prepare(const Fst<Arc> &fst) {
    if (finalized_) return;
    for (StateIterator<Fst<Arc> > siter(fst); !siter.Done(); siter.Next()) {
      StateId s = siter.Value();
      for (ArcIterator<Fst<Arc> > aiter(fst, s); !aiter.Done(); aiter.Next()) {
        const Arc &arc = aiter.Value();
        Label open_paren = OpenParenId(arc.ilabel);
        if (open_paren == arc.ilabel) {
          Arc open_arc(arc);
          StateId open_src = s, open_dest = open_arc.nextstate;
          open_arc.nextstate = open_src;
          open_arcs_.insert(make_pair(ParenState<Arc>(open_paren, open_dest), open_arc));
        } else if (open_paren != kNoLabel) {
          StateId close_src = s;
          close_arcs_.insert(make_pair(ParenState<Arc>(open_paren, close_src), arc));
        }
      }
    }
  }

  // Should be called after all close paren arcs have been seen
  void Finalize() {
    finalized_ = true;
  }

  void ReportOpenParen(StateId open_dest, StateId close_src, Label open_paren) {
    // Make sure there is close_src - open_paren -> ...
    if (close_arcs_.find(ParenState<Arc>(open_paren, close_src)) != close_arcs_.end())
      ReportReacheable(open_dest, close_src, open_paren);
  }

  void ReportCloseParen(StateId open_dest, StateId close_src, Label open_paren) {
    // Make sure there is ... - open_paren -> open_dest
    if (open_arcs_.find(ParenState<Arc>(open_paren, open_dest)) != open_arcs_.end())
      ReportReacheable(open_dest, close_src, open_paren);
  }

  // Returns an Iterator through all open paren arcs reachable to
  // close_src with a matching paren.
  OpenIterator FindOpen(Label open_paren, StateId close_src) const {
    typename ReachMap::const_iterator it = open_map_.find(ParenState<Arc>(open_paren, close_src));
    if (it == open_map_.end())
      return OpenIterator();
    else
      return OpenIterator(open_paren, it->second, open_arcs_);
  }

  // Returns an Iterator through all close paren arcs reachable from
  // open_dest with a matching paren.
  CloseIterator FindClose(Label open_paren, StateId open_dest) const {
    typename ReachMap::const_iterator it = close_map_.find(ParenState<Arc>(open_paren, open_dest));
    if (it == close_map_.end())
      return CloseIterator();
    else
      return CloseIterator(open_paren, it->second, close_arcs_);
  }

 private:
  // Maps each paren label to its open paren label
  void AssignParenId(const vector<pair<Label, Label> > parens) {
    for (typename vector<pair<Label, Label> >::const_iterator it = parens.begin();
         it != parens.end(); ++it) {
      open_paren_[it->first] = open_paren_[it->second] = it->first;
    }
  }

  void ReportReacheable(StateId open_dest, StateId close_src, Label open_paren) {
    open_map_[ParenState<Arc>(open_paren, close_src)].insert(open_dest);
    close_map_[ParenState<Arc>(open_paren, open_dest)].insert(close_src);
  }

  bool finalized_;
  ParenIdMap open_paren_;
  ReachMap open_map_, close_map_;
  ArcMap open_arcs_, close_arcs_;
};

} // namespace pdt
} // namespace fst

#endif  // FST_EXTENSIONS_PDT_PAREN_DATA_H__
