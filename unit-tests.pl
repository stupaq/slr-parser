:- use_module(library(plunit)).
:- consult('slr1-parser.pl').

%% Official tests
% test(+GrammarName, +WordList)
test(NG, ListaSlow) :-
  grammar(NG, G),
  createSLR1(G, Automat, ok),
  checkWords(ListaSlow, Automat).

% checkWords(+WordList, +Automaton)
checkWords([], _) :-
  write('Koniec testu.\n').
checkWords([S|RS], Automat) :-
  format("  Slowo: ~p ", [S]),
  (accept(Automat, S) -> true; write('NIE ')),
    write('nalezy.\n'),
    checkWords(RS, Automat).

% LR(0)
grammar(ex1, [prod('E', [[nt('E'), '+', nt('T')], [nt('T')]]),
  prod('T', [[id], ['(', nt('E'), ')']])]).
% LR(0)
grammar(ex2, [prod('A', [[nt('A'), x], [x]])]).
% SLR(1)
grammar(ex3, [prod('A', [[x, nt('A')], [x]])]).
% not SLR(1)
grammar(ex4, [prod('A', [[x, nt('B')], [nt('B'), y], []]), prod('B', [[]])]).
% not SLR(1)
grammar(ex5, [prod('S', [[id], [nt('V'), ':=', nt('E')]]),
  prod('V', [[id], [id, '[', nt('E'), ']']]), prod('E', [[nt('V')]])]).
% not SLR(1)

%% My tests
grammar(ex6, [prod('A', [[x], [nt('B'), nt('B')]]), prod('B', [[x]])]).
grammar(ex7, [prod('S', [[nt('A')], [x,b]]), prod('A', [[a, nt('A'), b], [nt('B')]]),
  prod('B', [[y]])]).
grammar(ex8, [prod('S', [[nt('L'), '=', nt('R')], [nt('R')]]),
  prod('L', [['*', nt('R')], [a]]), prod('R', [[nt('L')]])]).
grammar(fl1, [prod('A', [[nt('B'),x]]), prod('B', [[]])]).

:- begin_tests(exported).

test(success, forall(member(Name, [ex1,ex2,ex3,ex7]))) :-
  grammar(Name, Grammar),
  createSLR1(Grammar, Auto, ok),
  Auto = slr1([_ | _]).
test(conflict, forall(member(Name, [ex4,ex5,ex6,ex8]))) :-
  grammar(Name, Grammar),
  createSLR1(Grammar, Auto, konflikt(_)),
  Auto = null.
test(accept, forall(member((Name, Word), [
      (ex1, [id]),
      (ex1, ['(',id,')']),
      (ex1, [id,'+',id]),
      (ex1, ['(','(',id,'+','(',id,'+',id,')',')',')']),
      (ex1, [id,'+',id,'+','id']),
      (ex2, [x,x,x,x,x,x]),
      (ex2, [x,x,x,x,x]),
      (ex2, [x,x,x,x,x,x,x,x,x,x,x,x]),
      (ex3, [x,x,x,x,x,x]),
      (ex3, [x,x,x,x,x]),
      (ex3, [x,x,x,x,x,x,x,x,x,x,x,x]),
      (ex7, [y]),
      (ex7, [x,b]),
      (ex7, [a,a,a,a,y,b,b,b,b]),
      (ex7, [a,a,a,y,b,b,b])
    ]))) :-
  grammar(Name, Grammar),
  createSLR1(Grammar, Auto, ok),
  accept(Auto, Word).
test(reject, forall(member((Name, Word), [
      (ex1, [id,'+',ident]),
      (ex1, ['(','(',id,'+','(',id,'+',id,')',')']),
      (ex1, [id,'+',id,'+',id,'+']),
      (ex1, []),
      (ex2, [y]),
      (ex3, [y]),
      (ex3, []),
      (ex7, [y,x,b]),
      (ex7, [a,a,a,y,b,b]),
      (ex7, [a,x,b,a]),
      (ex7, [])
    ]))) :-
  grammar(Name, Grammar),
  createSLR1(Grammar, Auto, ok),
  \+ accept(Auto, Word).
test(follow, forall(member((Name, Follow), [
      (ex1, [follow('E',['+',')','#']),follow('T',['+',')','#'])]),
      (ex2, [follow('A',[x,'#'])]),
      (ex3, [follow('A',['#'])]),
      (ex4, [follow('A',['#']),follow('B',[y,'#'])]),
      (ex5, [follow('S',['#']),follow('V',[']',':=','#']),follow('E',[']','#'])]),
      (ex6, [follow('A',['#']),follow('B',[x,'#'])]),
      (ex7, [follow('S',['#']),follow('A',[b,'#']),follow('B',[b,'#'])]),
      (ex8, [follow('S',['#']),follow('L',['=','#']),follow('R',['=','#'])]),
      (fl1, [follow('A',['#']),follow('B',[x])])
    ]))) :-
  grammar(Name, Grammar),
  follow(Grammar, Answer),
  sort(Answer, Set),
  sort(Follow, Set).

:- end_tests(exported).
