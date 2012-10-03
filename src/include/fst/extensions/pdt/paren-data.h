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

} // namespace pdt
} // namespace fst

namespace std {
namespace tr1 {
template <class Arc>
struct hash<fst::pdt::FullArc<Arc> > {
  size_t operator()(const fst::pdt::FullArc<Arc> &fa) const {
    size_t value = fa.state;
    value = 1000003 * value ^ fa.arc.ilabel;
    value = 1000003 * value ^ fa.arc.olabel;
    value = 1000003 * value ^ fa.arc.nextstate;
    value = 1000003 * value ^ fa.arc.weight.Hash();
    return value;
  }
};
} // namespace tr1
} // namespace std


namespace fst {
namespace pdt {
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
  typedef const FullArc<Arc> *FullArcPtr;
  typedef unordered_set<FullArc<Arc> > FullArcSet;
  typedef unordered_set<FullArcPtr> FullArcPtrSet;
  typedef unordered_multimap<ParenState<Arc>, FullArcPtr, typename ParenState<Arc>::Hash> ParenArcMap;
  typedef unordered_map<ParenState<Arc>, FullArcPtrSet, typename ParenState<Arc>::Hash> SureMap;
  // typedef unordered_multimap<StateId, StateId> SubFinalMap;

 public:
  // Iterator through full arcs
  class Iterator {
   public:
    bool Done() const {
      return at_ == end_;
    }

    void Next() {
      ++at_;
    }

    const FullArc<Arc> &Value() const {
      return **at_;
    }

   private:
    typedef typename FullArcPtrSet::const_iterator SetIter;
    Iterator() : at_(), end_() {}
    Iterator(SetIter begin, SetIter end) :
        at_(begin), end_(end) {}
    SetIter at_, end_;
    template <class A>
    friend class PdtParenData;
  };

  // // Iterator through sub-final states
  // class SubFinalIterator {
  //  public:
  //   bool Done() const {
  //     return at_ == end_;
  //   }

  //   void Next() {
  //     ++at_;
  //   }

  //   StateId Value() const {
  //     return at_->second;
  //   }

  //  private:
  //   typedef typename SubFinalMap::const_iterator MapIter;
  //   SubFinalIterator() : at_(), end_() {}
  //   SubFinalIterator(MapIter begin, MapIter end) :
  //       at_(begin), end_(end) {}

  //   MapIter at_, end_;
  //   template <class A> friend class PdtParenData;
  // };

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

  // Finds all open paren arcs
  void Prepare(const Fst<Arc> &fst) {
    if (finalized_) return;
    for (StateIterator<Fst<Arc> > siter(fst); !siter.Done(); siter.Next()) {
      StateId s = siter.Value();
      for (ArcIterator<Fst<Arc> > aiter(fst, s); !aiter.Done(); aiter.Next()) {
        const Arc &arc = aiter.Value();
        Label open_paren = OpenParenId(arc.ilabel);
        if (open_paren == arc.ilabel) {
          FullArcPtr fa_ptr = FindOrAddArc(s, arc);
          open_arcs_.insert(make_pair(ParenState<Arc>(open_paren, arc.nextstate), fa_ptr));
        } else if (open_paren != kNoLabel) {
          FullArcPtr fa_ptr = FindOrAddArc(s, arc);
          close_arcs_.insert(make_pair(ParenState<Arc>(open_paren, fa_ptr->state), fa_ptr));
        }
      }
    }
  }

  // Should be called after all close paren arcs have been seen
  void Finalize() {
    open_arcs_.clear();
    close_arcs_.clear();
    finalized_ = true;
  }

  void ReportOpenParen(StateId open_src, const Arc &open_arc, StateId close_src, Label open_paren) {
    FullArcPtr open_fa_ptr = FindOrAddArc(open_src, open_arc);
    StateId open_dest = open_arc.nextstate;
    for (typename ParenArcMap::const_iterator it = close_arcs_.find(ParenState<Arc>(open_paren, close_src));
         it != open_arcs_.end() && it->first == ParenState<Arc>(open_paren, close_src); ++it) {
      FullArcPtr close_fa_ptr = it->second;
      open_map_[ParenState<Arc>(open_paren, close_src)].insert(open_fa_ptr);
      close_map_[ParenState<Arc>(open_paren, open_dest)].insert(close_fa_ptr);
    }
  }

  void ReportCloseParen(StateId open_dest, Label open_paren, StateId close_src, const Arc &close_arc) {
    FullArcPtr close_fa_ptr = FindOrAddArc(close_src, close_arc);
    for (typename ParenArcMap::const_iterator it = open_arcs_.find(ParenState<Arc>(open_paren, open_dest));
         it != open_arcs_.end() && it->first == ParenState<Arc>(open_paren, open_dest); ++it) {
      FullArcPtr open_fa_ptr = it->second;
      open_map_[ParenState<Arc>(open_paren, close_src)].insert(open_fa_ptr);
      close_map_[ParenState<Arc>(open_paren, open_dest)].insert(close_fa_ptr);
    }
  }

  // Returns an Iterator through all open paren arcs reachable to
  // close_src with a matching paren.
  Iterator FindOpen(Label open_paren, StateId close_src) const {
    return Find(open_paren, close_src, open_map_);
  }

  // Returns an Iterator through all close paren arcs reachable from
  // open_dest with a matching paren.
  Iterator FindClose(Label open_paren, StateId open_dest) const {
    return Find(open_paren, open_dest, close_map_);
  }

  // void ReportSubFinal(StateId substart, StateId subfinal) {
  //   subfinals_.insert(make_pair(substart, subfinal));
  // }

  // SubFinalIterator FindSubFinal(StateId substart) {
  //   pair<typename SubFinalMap::const_iterator, typename SubFinalMap::const_iterator> p =
  //       subfinals_.equal_range(substart);
  //   return SubFinalIterator(p.first, p.second);
  // }

 private:
  // Maps each paren label to its open paren label
  void AssignParenId(const vector<pair<Label, Label> > parens) {
    for (typename vector<pair<Label, Label> >::const_iterator it = parens.begin();
         it != parens.end(); ++it) {
      open_paren_[it->first] = open_paren_[it->second] = it->first;
    }
  }

  Iterator Find(Label paren, StateId state, const SureMap &map) const {
    typename SureMap::const_iterator it = map.find(ParenState<Arc>(paren, state));
    if (it == map.end())
      return Iterator();
    else
      return Iterator(it->second.begin(), it->second.end());
  }

  FullArcPtr FindOrAddArc(StateId src, const Arc &arc) {
    return &(*full_arcs_.insert(FullArc<Arc>(src, arc)).first);
  }

  bool finalized_;
  ParenIdMap open_paren_;
  SureMap open_map_, close_map_;
  ParenArcMap open_arcs_, close_arcs_;
  FullArcSet full_arcs_;
  // SubFinalMap subfinals_;
};

} // namespace pdt
} // namespace fst

#endif  // FST_EXTENSIONS_PDT_PAREN_DATA_H__
