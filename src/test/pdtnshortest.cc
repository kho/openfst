#include "pdtnshortest.h"

#include <fst/fstlib.h>
#include <fst/extensions/pdt/paren-data.h>
#include <fst/extensions/pdt/inside-outside.h>
#include <fst/extensions/pdt/n-shortest-path.h>
#include <fst/extensions/pdt/shortest-path.h>

#include <iostream>
#include <string>
#include <utility>
#include <vector>

using namespace std;

namespace fst {
vector<StopWatch> *StopWatch::pool_(NULL);

inline void StopWatch::Init() {
  if (pool_) return;
  pool_ = new vector<StopWatch>;
}

inline void StopWatch::Destroy() {
  delete pool_;
}

inline StopWatch *StopWatch::Get(Id n) {
  if (n)
    return &pool_->at(n-1);
  else
    return NULL;
}

inline StopWatch::Id StopWatch::New() {
  pool_->push_back(StopWatch());
  return pool_->size();
}

inline void StopWatch::Reset() {
  laps_.clear();
}

inline void StopWatch::Lap(const std::string &comment) {
  clock_t clk = clock();
  laps_.push_back(make_pair(clk - last_, comment));
  last_ = clock();
}

void StopWatch::Report(ostream &output) {
  for (vector<pair<clock_t, string> >::const_iterator it = laps_.begin();
       it != laps_.end(); ++it) {
    output << it->second << ": "
           << static_cast<double>(it->first) / CLOCKS_PER_SEC * 1000.0
           << "ms" << endl;
  }
}


} // namespace fst

using namespace fst;
using namespace fst::pdt;

typedef StdArc::Label Label;
typedef StdArc::StateId StateId;
typedef StdArc::Weight Weight;

StdArc A(Label l, Weight w, StateId dest) {
  return StdArc(l, l, w, dest);
}

vector<pair<Label, Label> > PARENS;

void Init() {
  PARENS.push_back(make_pair(1, 2));
  PARENS.push_back(make_pair(3, 4));
  PARENS.push_back(make_pair(5, 6));
  PARENS.push_back(make_pair(7, 8));
}

VectorFst<StdArc> *SimpleCyclic() {
  VectorFst<StdArc> m;
  StateId q[10];

  for (int i = 0; i < 10; ++i)
    q[i] = m.AddState();

  m.SetStart(q[0]);

  m.AddArc(q[0], A(1, 1, q[1]));
  m.AddArc(q[0], A(5, 5, q[4]));

  m.AddArc(q[1], A(9, 9, q[2]));

  m.AddArc(q[2], A(2, 2, q[3]));
  m.AddArc(q[2], A(8, 8, q[6]));

  m.AddArc(q[3], A(3, 3, q[4]));

  m.AddArc(q[4], A(10, 10, q[5]));

  m.AddArc(q[5], A(4, 4, q[6]));
  m.AddArc(q[5], A(6, 6, q[7]));

  m.SetFinal(q[6], Weight::One());

  m.AddArc(q[7], A(7, 7, q[1]));

  for (int i = 1; i <= 8; ++i)
    m.AddArc(q[8], A(i, 1, q[9]));

  return m.Copy();
}

namespace std { namespace tr1 {
template <>
struct hash<pair<int, int> > {
  size_t operator()(const pair<int, int> &p) const {
    return 7853 * p.first ^ p.second;
  }
};
} }

template <class Arc>
void InsideOutside(const Fst<Arc> &fst, const vector<pair<typename Arc::Label, typename Arc::Label> > &parens) {
  PdtParenData<Arc> pdata(parens);
  InsideOutsideChart<Arc> chart;

  StopWatch &watch = *StopWatch::Get(StopWatch::New());

  InsideAlgo<Arc>(fst, parens, &pdata).FillChart(&chart);
  watch.Lap("inside");

  OutsideAlgo<Arc>(fst, parens, &pdata).FillChart(&chart);
  watch.Lap("outside");

  watch.Report(cerr);
}

int main(int argc, char *argv[]) {
  Init();
  StopWatch::Init();

  PdtNShortestPathTester<StdArc> tester(StopWatch::New(), true);

  if (argc == 4) {
    string op(argv[1]), fst_in(argv[2]), parens_in(argv[3]);
    VectorFst<StdArc> fst(*VectorFst<StdArc>::Read(fst_in));
    vector<pair<StdArc::Label, StdArc::Label> > parens;
    ReadLabelPairs(parens_in, &parens);

    size_t num_arcs = 0;
    for (StateIterator<VectorFst<StdArc> > it(fst); !it.Done(); it.Next())
      num_arcs += fst.NumArcs(it.Value());

    VLOG(0) << "pdt has " << CountStates(fst) << " states, " << num_arcs << " arcs and "
            << parens.size() << " pairs of parens";

    if (op == "io")
      InsideOutside(fst, parens);
    else if (op == "test")
      tester.Test(fst, parens);
    else if (op == "time")
      tester.Time(fst, parens);
    else if (op == "comp") {
      {
        VectorFst<StdArc> o;
        Timer::Get(1).Start();
        ShortestPath(fst, parens, &o);
        Timer::Get(1).Record("ShortestPath");
      }
      {
        VectorFst<StdArc> o;
        Timer::Get(1).Start();
        NShortestPath(fst, parens, &o, 1);
        Timer::Get(1).Record("A*-1");
      }
      {
        VectorFst<StdArc> o;
        Timer::Get(1).Start();
        NShortestPath(fst, parens, &o, 1);
        Timer::Get(1).Record("A*-1");
      }
      {
        VectorFst<StdArc> o;
        Timer::Get(1).Start();
        NShortestPath(fst, parens, &o, 10);
        Timer::Get(1).Record("A*-10");
      }
      {
        VectorFst<StdArc> o;
        Timer::Get(1).Start();
        NShortestPath(fst, parens, &o, 100);
        Timer::Get(1).Record("A*-100");
      }
      {
        VectorFst<StdArc> o;
        Timer::Get(1).Start();
        NShortestPath(fst, parens, &o, 1000);
        Timer::Get(1).Record("A*-1000");
      }
      {
        VectorFst<StdArc> o;
        Timer::Get(1).Start();
        NShortestPath(fst, parens, &o, 10000);
        Timer::Get(1).Record("A*-10000");
      }
      {
        VectorFst<StdArc> o;
        Timer::Get(1).Start();
        NShortestPath(fst, parens, &o, 1, true);
        Timer::Get(1).Record("Lazy-1");
      }
      {
        VectorFst<StdArc> o;
        Timer::Get(1).Start();
        NShortestPath(fst, parens, &o, 1, true);
        Timer::Get(1).Record("Lazy-1");
      }
      {
        VectorFst<StdArc> o;
        Timer::Get(1).Start();
        NShortestPath(fst, parens, &o, 10, true);
        Timer::Get(1).Record("Lazy-10");
      }
      {
        VectorFst<StdArc> o;
        Timer::Get(1).Start();
        NShortestPath(fst, parens, &o, 100, true);
        Timer::Get(1).Record("Lazy-100");
      }
      {
        VectorFst<StdArc> o;
        Timer::Get(1).Start();
        NShortestPath(fst, parens, &o, 1000, true);
        Timer::Get(1).Record("Lazy-1000");
      }
      {
        VectorFst<StdArc> o;
        Timer::Get(1).Start();
        NShortestPath(fst, parens, &o, 10000, true);
        Timer::Get(1).Record("Lazy-10000");
      }
    } else
      VLOG(0) << "Unknown op: " << op;
  } else {
    // simple test
    VectorFst<StdArc> fst(*SimpleCyclic());
    tester.Test(fst, PARENS);
  }

  StopWatch::Destroy();
  return 0;
}
