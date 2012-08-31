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

  // Arc and its source state
  struct FullArc {
    FullArc(StateId s, const Arc &a): state(s), arc(a) {}
    StateId state;
    Arc arc;

    bool operator==(const FullArc &that) const {
      return this == &that || (state = that.state && arc == that.arc);
    }

    struct Hash {
      size_t operator()(const FullArc &fa) {
        size_t value = fa.state;
        value = 1000003 * value ^ fa.arc.ilabel;
        value = 1000003 * value ^ fa.arc.olabel;
        value = 1000003 * value ^ fa.arc.nextstate;
        value = 1000003 * value ^ fa.arc.weight.Hash();
        return value;
      }
    };
  };

  // Iterator through full arcs
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
    typedef typename ArcSet::const_iterator SetIter;
    Iterator() : at_(), end_() {}
    Iterator(SetIter begin, SetIter end) :
        at_(begin), end_(end) {}
    SetIter at_, end_;
  };

  // The constructor does not initialize the mapping; Init() must also
  // be called.
  PdtParenData(const Fst<Arc> &ifst, const vector<pair<Label, Label> > &parens) :
      ifst_(ifst.Copy()), parens_(parens), clear_(false) {}

  ~PdtParenData() {
    delete ifst_;
  }

  // Inits to naive mapping, i.e. stores all opening/closing arcs by
  // their open paren. This must be called before accessing any paren
  // information.
  void Init() {
    AssignParenId();
    NaiveMapping();
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
    typename unordered_map<Label, Label>::const_iterator it = open_paren_.find(l);
    if (it == open_paren_.end())
      return kNoLabel;
    else
      return it->second;
  }

  // Reports a pair of matching paren arcs. After ClearNaive() these
  // will be used to provide more accurate answer to open/close arc
  // queries.
  void ReportUseful(StateId open_src, const Arc &open_arc,
                    StateId close_src, const Arc &close_arc) {
    Label open_paren = OpenParenId(open_arc.ilabel);
    sure_open_map_[ParenState<Arc>(open_paren, close_src)].insert(FullArc(open_src, open_arc));
    sure_close_map_[ParenState<Arc>(open_paren, open_arc.nextstate)].insert(FullArc(close_src, close_arc));
  }

  // Notifies that all useful pairs have been reported; thus
  // PdtParenData can discard the naive mappings and start using the
  // sure mappings.
  void ClearNaive() {
    if (!clear_) {
      naive_open_map_.clear();
      naive_close_map_.clear();
      clear_ = true;
    }
  }

  // Returns an Iterator through all open paren arcs reachable to
  // close_src with a matching paren.
  Iterator FindOpen(Label open_paren, StateId close_src) const {
    if (clear_)
      return FindSure(open_paren, close_src, sure_open_map_);
    else
      return FindNaive(open_paren, naive_open_map_);
  }

  // Returns an Iterator through all close paren arcs reachable from
  // open_dest with a matching paren.
  Iterator FindClose(Label open_paren, StateId open_dest) const {
    if (clear_)
      return FindSure(open_paren, open_dest, sure_close_map_);
    else
      return FindNaive(open_paren, naive_close_map_);
  }

 private:
  typedef unordered_set<FullArc, typename FullArc::Hash> ArcSet;
  typedef unordered_map<Label, ArcSet> NaiveMap;
  typedef unordered_map<ParenState<Arc>, ArcSet, typename ParenState<Arc>::Hash> SureMap;

  // Maps each paren label to its open paren label
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
