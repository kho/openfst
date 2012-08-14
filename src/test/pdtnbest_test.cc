#include <fst/fstlib.h>
#include <fst/extensions/pdt/n-shortest-path.h>
#include <fst/extensions/pdt/shortest-path.h>

#include <fst/script/draw-impl.h>

#include <iostream>
#include <utility>
#include <vector>

using namespace fst;
using namespace std;

typedef StdArc::Label Label;
typedef StdArc::StateId StateId;
typedef StdArc::Weight Weight;

StdArc A(Label l, Weight w, StateId dest) {
  return StdArc(l, l, w, dest);
}

template <class Arc> inline
void DrawFst(const Fst<Arc> &fst, ostream &output) {
  FstDrawer<Arc> drawer(fst,
                        fst.InputSymbols(), fst.OutputSymbols(), NULL,
                        true, "", 16, 9,
                        true, false,
                        0.40, 0.25,
                        14, 5,
                        false);
  drawer.Draw(&output, "");
}

SymbolTable SYM("global");
vector<pair<Label, Label> > PARENS;

void Init() {
  // Symbol table:
  // a : 1
  // b : 2
  // c : 3
  // d : 4
  // ( : 5
  // ) : 6
  // [ : 7
  // ] : 8
  SYM.AddSymbol("eps", 0);
  SYM.AddSymbol("a", 1);
  SYM.AddSymbol("b", 2);
  SYM.AddSymbol("c", 3);
  SYM.AddSymbol("d", 4);
  SYM.AddSymbol("(", 5);
  SYM.AddSymbol(")", 6);
  SYM.AddSymbol("[", 7);
  SYM.AddSymbol("]", 8);
  PARENS.push_back(make_pair(5, 6));
  PARENS.push_back(make_pair(7, 8));
}

void SimpleAcyclic(bool kp) {
  VectorFst<StdArc> m;
  m.SetInputSymbols(&SYM);
  m.SetOutputSymbols(&SYM);

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


  PdtNShortestPathOptions opts(10, 0, false, kp);
  PdtNShortestPath<StdArc> solver(m, PARENS, opts);

  VectorFst<StdArc> mm;
  size_t n_found = solver.NShortestPath(&mm);

  cerr << "Found " << n_found << " paths." << endl;
  DrawFst(mm, cout);
}

void SimpleCyclic(bool kp) {
  VectorFst<StdArc> m;
  m.SetInputSymbols(&SYM);
  m.SetOutputSymbols(&SYM);

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

  PdtNShortestPathOptions opts(5, 0, false, kp);
  PdtNShortestPath<StdArc> solver(m, PARENS, opts);

  VectorFst<StdArc> mm;
  size_t n_found = solver.NShortestPath(&mm);

  cerr << "Found " << n_found << " paths." << endl;
  DrawFst(mm, cout);

  // This will give an error:
  // ShortestPath(m, PARENS, &mm);
}

int main(int argc, char *argv[]) {
  bool kp = false;
  if (argc > 1 && string(argv[1]) == string("-k"))
    kp = true;
  Init();
  SimpleAcyclic(kp);
  SimpleCyclic(kp);
  return 0;
}

