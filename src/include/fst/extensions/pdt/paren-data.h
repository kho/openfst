// paren-data.h
//
// \file
// Metadata of parentheses

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
//
// PdtParenData: provides closing/opening arcs for opening/closing
// parentheses and states; also assigns paren ids.
//
template <class Arc>
class PdtParenData {
 public:
  typedef typename Arc::Label Label;
  typedef typename Arc::StateId StateId;
  typedef typename Arc::Weight Weight;

  struct FullArc {
    FullArc(StateId s, const Arc &a): state(s), arc(a) {}
    StateId state;
    Arc arc;

    bool operator==(const FullArc &that) const {
      return this == &that || (state = that.state && arc == that.arc);
    }

    struct Hash {
      size_t operator()(const FullArc &fa) {
        size_t value = 0x345678;
        value = 1000003 * value ^ fa.state;
        value = 1000003 * value ^ fa.arc.ilabel;
        value = 1000003 * value ^ fa.arc.olabel;
        value = 1000003 * value ^ fa.arc.nextstate;
        value = 1000003 * value ^ fa.arc.weight.Hash();
        return value;
      }
    };
  };

  class Iterator {
   public:
    bool Done() const {
      return at_ == end_;
    }

    void Next() {
      ++at_;
    }

    const FullArc &Value() const {
      return *at_;
    }

   private:
    typedef typename unordered_set<FullArc, typename FullArc::Hash>::const_iterator SetIter;
    Iterator() : at_(), end_() {}
    Iterator(SetIter begin, SetIter end) :
        at_(begin), end_(end) {}
    SetIter at_, end_;
  };

  PdtParenData(const Fst<Arc> &ifst, const vector<pair<Label, Label> > &parens) :
      ifst_(ifst.Copy()), parens_(parens), clear_(false) {}

  void Init() {
    AssignParenId();
    NaiveMapping();
  }

  Label OpenParenId(Label l) const {
    typename unordered_map<Label, Label>::const_iterator it = open_paren_.find(l);
    if (it == open_paren_.end())
      return kNoLabel;
    else
      return *it;
  }

  void ReportUseful(StateId open_src, const Arc &open_arc,
                    StateId close_src, const Arc &close_arc) {
    Label open_paren = OpenParenId(open_arc.label);
    sure_open_map_[ParenState<Arc>(open_paren, close_src)].insert(FullArc(open_src, open_arc));
    sure_close_map_[ParenState<Arc>(open_paren, open_arc.nextstate)].insert(FullArc(close_src, close_arc));
  }

  void ClearNaive() {
    if (!clear_) {
      naive_open_map_.clear();
      naive_close_map_.clear();
      clear_ = true;
    }
  }

  Iterator FindOpen(Label open_paren, StateId close_src) const {
    if (clear_)
      return FindSure(open_paren, close_src, sure_open_map_);
    else
      return FindNaive(open_paren, naive_open_map_);
  }

  Iterator FindClose(Label open_paren, StateId open_dest) const {
    if (clear_)
      return FindSure(open_paren, open_dest, sure_close_map_);
    else
      return FindNaive(open_paren, naive_close_map_);
  }

 private:
  typedef unordered_map<Label, unordered_set<FullArc, typename FullArc::Hash> > NaiveMap;
  typedef unordered_map<ParenState<Arc>, unordered_set<FullArc, typename FullArc::Hash>, typename ParenState<Arc>::Hash> SureMap;

  // Assigns paren id
  void AssignParenId() {
    for (typename vector<pair<Label, Label> >::const_iterator it = parens_.begin();
         it != parens_.end(); ++it) {
      open_paren_[it->first] = open_paren_[it->second] = it->first;
    }
  }

  // Naive open/close paren mapping; simply stores all paired arcs for each paren label
  void NaiveMapping() {
    for (StateIterator<Fst<Arc> > siter(*ifst_); !siter.Done(); siter.Next()) {
      StateId s = siter.Value();
      for (ArcIterator<Fst<Arc> > aiter(*ifst_, s); !aiter.Done(); aiter.Next()) {
        const Arc &arc = aiter.Value();
        Label open_paren = OpenParenId(arc.label);
        if (open_paren != kNoLabel) {   // paren
          if (open_paren == arc.label)  // open
            naive_open_map_[open_paren].insert(FullArc(s, arc));
          else                          // close
            naive_close_map_[open_paren].insert(FullArc(s, arc));
        }
      }
    }
  }

  Iterator FindSure(Label paren, StateId state, const SureMap &map) const {
    typename SureMap::const_iterator it = map.find(ParenState<Arc>(paren, state));
    if (it == map.end())
      return Iterator();
    else
      return Iterator(it->begin(), it->end());
  }

  Iterator FindNaive(Label paren, const NaiveMap &map) const {
    typename NaiveMap::const_iterator it = map.find(paren);
    if (it == map.end())
      return Iterator();
    else
      return Iterator(it->begin(), it->end());
  }

  const Fst<Arc> *ifst_;
  const vector<pair<Label, Label> > &parens_;

  unordered_map<Label, Label> open_paren_;
  NaiveMap naive_open_map_, naive_close_map_;
  SureMap sure_open_map_, sure_close_map_;
  bool clear_;
};

} // namespace pdt
} // namespace fst

#endif  // FST_EXTENSIONS_PDT_PAREN_DATA_H__
