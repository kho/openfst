// pdtnshortest_test.h

#ifndef FST_TEST_PDTNSHORTEST_H__
#define FST_TEST_PDTNSHORTEST_H__

#include <fst/fstlib.h>
#include <fst/extensions/pdt/compose.h>
#include <fst/extensions/pdt/expand.h>
#include <fst/extensions/pdt/shortest-path.h>
#include <fst/extensions/pdt/n-shortest-path.h>

#include <ctime>
using std::clock_t;
#include <iostream>
using std::ostream;
#include <set>
using std::set;
#include <sstream>
#include <string>
using std::string;
#include <utility>
using std::pair;
#include <vector>
using std::vector;

namespace fst {

class StopWatch {
 public:
  typedef vector<StopWatch>::size_type Id;

  static void Init();
  static void Destroy();
  static Id New();
  static StopWatch *Get(Id);

  void Reset();
  void Lap(const string &);
  void Report(ostream &);

 private:
  static vector<StopWatch> *pool_;
  vector<pair<clock_t, string> > laps_;
  clock_t last_;
};

template <class Arc>
class PdtNShortestPathTester {
 public:
  typedef typename Arc::Label Label;
  typedef typename Arc::StateId StateId;
  typedef typename Arc::Weight Weight;

  typedef vector<pair<Label, Label> > Parens;

  PdtNShortestPathTester(StopWatch::Id watch = 0, bool verbose = false) :
      watch_(StopWatch::Get(watch)), verbose_(verbose) {}

  void Test(const Fst<Arc> &fst, const Parens &parens) {
    TestSingleShortest(fst, parens);
    TestNShortest(fst, parens, 1000);
  }

  void Time(const Fst<Arc> &fst, const Parens &parens) {
    if (!watch_)
      FSTERROR() << "PdtNShortestPathTester: no stop watch";
    // TimeVariousN(fst, parens, 10, 10, 1000 + 1);
    // TimeSingleShortest(fst, parens);
    TimeNShortest(fst, parens, 1000);
  }

 private:
  struct PathComp {
    bool operator()(const pair<vector<Label>, Weight> &x,
                    const pair<vector<Label>, Weight> &y) {
      if (x.second != y.second) {
        Weight a = Plus(x.second, y.second);
        return a == x.second;
      } else {
        return x.first <= y.first;
      }
    }
  };

  void TestSingleShortest(const Fst<Arc> &fst, const Parens &parens) {
    VectorFst<Arc> ofst1, ofst2;
    ShortestPath(fst, parens, &ofst1);
    if (verbose_) VLOG(0) << "TestSingleShortest: " << "ShortestPath finished";
    NShortestPath(fst, parens, &ofst2, 1);
    if (verbose_) VLOG(0) << "TestSingleShortest: " << "NShortestPath finished";
    CHECK(EquivPaths(fst, parens, ofst1, ofst2));
    if (verbose_)
      VLOG(0) << "TestSingleShortest: " << "pass";
  }

  void TestNShortest(const Fst<Arc> &fst, const Parens &parens, size_t n) {
    VectorFst<Arc> ofst1, ofst2;
    NShortestPath(fst, parens, &ofst2, n);
    if (verbose_) VLOG(0) << "TestNShortest: " << "NShortestPath finished";
    NShortestPathViaExpand(fst, parens, &ofst1, n);
    if (verbose_) VLOG(0) << "TestNShortest: " << "NShortestPathViaExpand finished";
    CHECK(EquivPaths(fst, parens, ofst1, ofst2));
    if (verbose_)
      VLOG(0) << "TestNShortest: " << "pass";
  }

  void TimeVariousN(const Fst<Arc> &fst, const Parens &parens, size_t start, size_t step, size_t stop) {
    for (size_t n = start; n < stop; n += step) {
      VectorFst<Arc> ofst;
      std::ostringstream o; o << n;
      string comment(o.str());
      watch_->Reset();
      NShortestPath(fst, parens, &ofst, n);
      watch_->Lap(comment);
      watch_->Report(std::cout);
    }
  }

  void TimeSingleShortest(const Fst<Arc> &fst, const Parens &parens) {
    VectorFst<Arc> ofst1, ofst2;
    string comment1("Old ShortestPath"), comment2("NShortestPath with N=1");

    watch_->Reset();
    ShortestPath(fst, parens, &ofst1);
    watch_->Lap(comment1);
    watch_->Report(std::cout);

    watch_->Reset();
    NShortestPath(fst, parens, &ofst2, 1);
    watch_->Lap(comment2);
    watch_->Report(std::cout);
  }

  void TimeNShortest(const Fst<Arc> &fst, const Parens &parens, size_t n) {
    VectorFst<Arc> ofst1, ofst2;
    string comment1("NShortestPathViaExpand"), comment2("NShortestPath");

    // watch_->Reset();
    // NShortestPathViaExpand(fst, parens, &ofst1, n);
    // watch_->Lap(comment1);
    // watch_->Report(std::cout);

    watch_->Reset();
    NShortestPath(fst, parens, &ofst2, n);
    watch_->Lap(comment2);
    watch_->Report(std::cout);
  }

  void NShortestPathViaExpand(const Fst<Arc> &fst, const Parens &parens, MutableFst<Arc> *ofst, size_t n) {
    VectorFst<Arc> expanded;
    Expand(fst, parens, &expanded);
    ShortestPath(expanded, ofst, n);
  }

  void GetPaths(const Fst<Arc> &fst, vector<pair<vector<Label>, Weight> > *output) {
    output->clear();

    if (fst.Start() == kNoStateId) return;

    for (ArcIterator<Fst<Arc> > aiter(fst, fst.Start()); !aiter.Done(); aiter.Next()) {
      const Arc &init_arc = aiter.Value();
      output->push_back(make_pair(vector<Label>(), Weight::One()));
      vector<Label> &p = output->back().first;
      Weight &w = output->back().second;

      if (init_arc.ilabel) p.push_back(init_arc.ilabel);
      w = Times(w, init_arc.weight);

      StateId s = kNoStateId;
      for (s = init_arc.nextstate; fst.Final(s) == Weight::Zero(); ) {
        ArcIterator<Fst<Arc> > next_aiter(fst, s);
        const Arc &next_arc = next_aiter.Value();

        if (next_arc.ilabel) p.push_back(next_arc.ilabel);
        w = Times(w, next_arc.weight);

        s = next_arc.nextstate;
      }

      w = Times(w, fst.Final(s));
    }
  }

  void UniquePaths(vector<pair<vector<Label>, Weight> > *output) {
    set<vector<Label> > seen_paths;

    vector<bool> remove(output->size(), false);
    for (size_t i = 0; i < output->size(); ++i) {
      if (!seen_paths.insert(output->at(i).first).second)
        remove[i] = true;
    }
    size_t next_pos = 1;
    for (size_t i = 1; i < output->size(); ++i) {
      if (!remove[i]) {
        output->at(next_pos) = output->at(i);
        ++next_pos;
      }
    }
    output->resize(next_pos);
  }

  bool EquivPaths(const Fst<Arc> &fst, const Parens &parens,
                  const Fst<Arc> &fst1, const Fst<Arc> &fst2, float delta = kDelta) {
    vector<pair<vector<Label>, Weight> > paths1, paths2;

    // vector<Label> empty_path;
    // empty_path.push_back(0);
    // cout << "Accepting " << AcceptingPath(fst, parens, empty_path) << endl;

    GetPaths(fst1, &paths1);
    UniquePaths(&paths1);
    GetPaths(fst2, &paths2);
    UniquePaths(&paths2);

    if (verbose_) {
      VLOG(0) << "fst1 has " << paths1.size() << " paths";
      VLOG(0) << "fst2 has " << paths2.size() << " paths";
      VLOG(0) << "precision tolerance: " << delta;
    }

    for (typename vector<pair<vector<Label>, Weight> >::size_type i = 0; i < paths1.size(); ++i) {
      if (!AcceptingPath(fst, parens, paths1[i].first)) {
        cout << i << "-th path(1) is not accepted" << endl;
        for (typename vector<Label>::const_iterator it = paths1[i].first.begin();
             it != paths1[i].first.end(); ++it)
          cout << " " << *it;
        cout << endl;
        return false;
      }
      if (!AcceptingPath(fst, parens, paths2[i].first)) {
        cout << i << "-th path(2) is not accepted" << endl;
        for (typename vector<Label>::const_iterator it = paths2[i].first.begin();
             it != paths2[i].first.end(); ++it)
          cout << " " << *it;
        cout << endl;
        return false;
      }
    }

    bool pass = true;
    size_t cmp_size = paths1.size() < paths2.size() ? paths1.size() : paths2.size();
    for (typename vector<pair<vector<Label>, Weight> >::size_type i = 0; i < cmp_size; ++i) {
      if (!ApproxEqual(paths1[i].second, paths2[i].second, delta)) {
        cout << i << "-th paths have different weights: " << endl;
        for (typename vector<Label>::const_iterator it = paths1[i].first.begin();
             it != paths1[i].first.end(); ++it)
          cout << " " << *it;
        cout << endl;
        for (typename vector<Label>::const_iterator it = paths2[i].first.begin();
             it != paths2[i].first.end(); ++it)
          cout << " " << *it;
        cout << endl;
        pass = false;
        break;
      }
    }

    if (!pass) {
      for (size_t i = 0; i < paths1.size(); ++i) {
        cout << "PATHS1 " << paths1[i].second;
        for (typename vector<Label>::const_iterator it = paths1[i].first.begin();
             it != paths1[i].first.end(); ++it)
          cout << " " << *it;
        cout << endl;
      }
      for (size_t i = 0; i < paths2.size(); ++i) {
        cout << "PATHS2 " << paths2[i].second;
        for (typename vector<Label>::const_iterator it = paths2[i].first.begin();
             it != paths2[i].first.end(); ++it)
          cout << " " << *it;
        cout << endl;
      }
    }

    return pass;
  }

  bool AcceptingPath(const Fst<Arc> &fst, const Parens &parens,
                     const vector<Label> &path) {
    VectorFst<Arc> path_fst, comp_fst, out_fst;
    StateId p, q;
    q = path_fst.AddState();
    path_fst.SetStart(q);
    for (typename vector<Label>::const_iterator it = path.begin();
         it != path.end(); ++it) {
      p = q;
      q = path_fst.AddState();
      path_fst.AddArc(p, Arc(*it, *it, Weight::One(), q));
    }
    path_fst.SetFinal(q, Weight::One());
    Compose(path_fst, fst, parens, &comp_fst);
    ShortestPath(comp_fst, parens, &out_fst);
    vector<pair<vector<Label>, Weight> > paths;
    GetPaths(out_fst, &paths);
    return paths.size() != 0;
  }

  StopWatch *watch_;
  bool verbose_;
};

} // namespace fst

#endif  // FST_TEST_PDTNSHORTEST_H__
