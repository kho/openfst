#include "pdtnshortest.h"

#include <fst/fstlib.h>
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

typedef StdArc::Label Label;
typedef StdArc::StateId StateId;
typedef StdArc::Weight Weight;

StdArc A(Label l, Weight w, StateId dest) {
  return StdArc(l, l, w, dest);
}

vector<pair<Label, Label> > PARENS;

void Init() {
  PARENS.push_back(make_pair(5, 6));
  PARENS.push_back(make_pair(7, 8));
}

VectorFst<StdArc> *SimpleAcyclic() {
  VectorFst<StdArc> m;
  StateId q[8];

  for (int i = 0; i < 8; ++i)
    q[i] = m.AddState();

  m.SetStart(q[0]);
  m.SetFinal(q[7], Weight::One());

  m.AddArc(q[0], A(1, -1, q[1]));
  m.AddArc(q[0], A(3, 5, q[2]));
  m.AddArc(q[0], A(4, 2, q[3]));

  m.AddArc(q[1], A(5, 0, q[3]));

  m.AddArc(q[2], A(7, 0, q[3]));

  m.AddArc(q[3], A(2, 0, q[4]));

  m.AddArc(q[4], A(6, 0, q[5]));
  m.AddArc(q[4], A(8, 0, q[6]));
  m.AddArc(q[4], A(4, 3, q[7]));

  m.AddArc(q[5], A(1, 5, q[7]));

  m.AddArc(q[6], A(3, 2, q[7]));

  return m.Copy();
}

VectorFst<StdArc> *SimpleCyclic() {
  VectorFst<StdArc> m;
  StateId q[4];

  for (int i = 0; i < 4; ++i)
    q[i] = m.AddState();

  m.SetStart(q[0]);
  m.SetFinal(q[1], Weight::One());
  m.SetFinal(q[3], Weight::One());

  m.AddArc(q[0], A(5, 0, q[1]));
  m.AddArc(q[0], A(2, 1, q[2]));

  m.AddArc(q[1], A(1, 1, q[0]));
  m.AddArc(q[1], A(1, 1, q[0]));

  m.AddArc(q[2], A(6, 0, q[3]));

  m.AddArc(q[3], A(2, 1, q[2]));

  return m.Copy();
}

int main(int argc, char *argv[]) {
  Init();
  StopWatch::Init();

  PdtNShortestPathTester<StdArc> tester(StopWatch::New(), true);

  do {
    // simple test
    VectorFst<StdArc> fst(*SimpleAcyclic());
    tester.Test(fst, PARENS);
  } while (false);

  if (argc == 3) {
    string fst_in(argv[1]), parens_in(argv[2]);
    VectorFst<StdArc> fst(*VectorFst<StdArc>::Read(fst_in));
    vector<pair<StdArc::Label, StdArc::Label> > parens;
    ReadLabelPairs(parens_in, &parens);

    VLOG(0) << "pdt has " << CountStates(fst) << " states and "
            << parens.size() << " pairs of parens";

    tester.Test(fst, parens);

    tester.Time(fst, parens);
  }

  StopWatch::Destroy();
  return 0;
}
