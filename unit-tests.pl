:- use_module(library(plunit)).
:- consult('slr1-parser.pl').

gr(ex7, [prod('S', [[nt('A')], [x,b]]), prod('A', [[a, nt('A'), b], [nt('B')]]),
  prod('B', [[y]])]).
gr(ex8, [prod('S', [[nt('L'), '=', nt('R')], [nt('R')]]),
  prod('L', [['*', nt('R')], [a]]), prod('R', [[nt('L')]])]).
gr(fl1, [prod('A', [[nt('B'),x]]), prod('B', [[]])]).

:- begin_tests(exported).

test(success, forall(member(Name, [ex1,ex2,ex3,ex7]))) :-
  (grammar(Name, Grammar); gr(Name, Grammar)),
  createSLR1(Grammar, Auto, ok),
  Auto = slr1([_ | _]).
test(conflict, forall(member(Name, [ex4,ex5,ex6,ex8]))) :-
  (grammar(Name, Grammar); gr(Name, Grammar)),
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
  (grammar(Name, Grammar); gr(Name, Grammar)),
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
  (grammar(Name, Grammar); gr(Name, Grammar)),
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
  (grammar(Name, Grammar); gr(Name, Grammar)),
  follow(Grammar, Answer),
  sort(Answer, Set),
  sort(Follow, Set).

:- end_tests(exported).
