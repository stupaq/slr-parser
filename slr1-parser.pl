% JPP; zadanie 3; Mateusz Machalica; 305678

:- use_module(library(lists)).
:- expects_dialect(sicstus).

% Exported
% createSLR1(+Grammar, -Automata, -Info)

% accept(+Automata, +Word)

% Entire follow/* logic requires all nonterminals to be reachable from
% grammar's start symbol

% follow(+Grammar, -FollowSets)
follow(Grammar, Set) :-
  setof(follow(N, NSet), follow(Grammar, nt(N), NSet), Set). % FIXME

% follow(+Grammar, +Nonterminal, -FollowSet)
follow(Grammar, nt(N), Set) :-
  setof(X, follow(Grammar, nt(N), X, []), Set). % FIXME
follow(Grammar, nt(N), []) :-
  nonterminal(Grammar, nt(N)),
  not(follow(Grammar, nt(N), _, [])).

% follow(+Grammar, +Nonterminal, +Terminal, +Guard)
follow(Grammar, nt(N), T, Guard) :-
  terminal(Grammar, T),
  rule(Grammar, nt(_), Rhs, Id),
  not(member(Id, Guard)),
  append([_, [nt(N)], B], Rhs),
  first(Grammar, B, T).
follow(Grammar, nt(N), T, Guard) :-
  terminal(Grammar, T),
  rule(Grammar, nt(X), Rhs, Id),
  not(member(Id, Guard)),
  append([_, [nt(N)], B], Rhs),
  nullable(Grammar, B),
  follow(Grammar, nt(X), T, [Id | Guard]).

% Grammar properties
% first(+Grammar, +SententialForm, +Terminal)
first(Grammar, Sentence, T) :-
  first(Grammar, Sentence, T, []).
% first(+Grammar, +SententialForm, +Terminal, +Guard)
first(_, [T | _], T, _).
first(Grammar, [nt(N) | _], T, Guard) :-
  rule(Grammar, nt(N), Rhs, Id),
  not(member(Id, Guard)), % first(Rhs, T) :- first(Rhs, T), ...
  first(Grammar, Rhs, T, [Id | Guard]).
first(Grammar, Sentence, T, Guard) :-
  append([A, B], Sentence),
  not(empty(A)),
  nullable(Grammar, A),
  first(Grammar, B, T, Guard).

% nullable(+Grammar, +SententialForm)
nullable(Grammar, Sentence) :-
  nullable(Grammar, Sentence, []).
% nullable(+Grammar, +SententialForm, +Guard)
nullable(_, [], _).
nullable(Grammar, [nt(N) | Rest], Guard) :-
  nullable(Grammar, nt(N), Guard),
  nullable(Grammar, Rest, Guard).
% nullable(+Grammar, +Nonterminal, +Guard)
nullable(Grammar, nt(N), Guard) :-
  rule(Grammar, nt(N), Rhs),
  not(intersect(Rhs, [N | Guard])), % nullable(A) :- nullable(A), ...
  nullable(Grammar, Rhs, [N | Guard]).

% Grammar accessors
% rule(+Grammar, +Nonterminal, -ProductionRhs)
rule([prod(N, RhsList) | _], nt(N), Rhs) :-
  member(Rhs, RhsList).
rule([_ | Rest], nt(N), Rhs) :-
  rule(Rest, nt(N), Rhs).

% rule(+Grammar, +Nonterminal, -ProductionRhs, -Ident)
rule(Grammar, nt(N), Rhs, ident(N, Rhs)) :-
  rule(Grammar, nt(N), Rhs).

% nonterminal(+Grammar, +Nonterminal)
nonterminal([prod(N, _) | _], nt(N)).
nonterminal([_ | Rest], nt(N)) :-
  nonterminal(Rest, nt(N)).

% terminal(+Grammar, +Terminal)
terminal([prod(_, RhsList) | _], T) :-
  append(RhsList, All),
  member(T, All),
  T \= nt(_).
terminal([_ | Rest], T) :-
  terminal(Rest, T).

% Helpers
% intersect(+List1, +List2)
intersect(List1, List2) :-
  member(X, List1),
  member(X, List2).

% empty(+List)
empty([]).

% Official tests
% test(+GrammarName, +WordList)
test(NG, ListaSlow) :-
  grammar(NG, G),
  createSLR1(G, Automat, ok),
  checkWords(ListaSlow, Automat).

% checkWords(+WordList, +Automata)
checkWords([], _) :-
  write('Koniec testu.\n').
checkWords([S|RS], Automat) :-
  format("  Slowo: ~p ", [S]),
  (accept(Automat, S) -> true; write('NIE ')),
    write('nalezy.\n'),
    checkWords(RS, Automat).

% LR(0)
grammar(ex1, [prod('E', [[nt('E'), '+', nt('T')], [nt('T')]]), prod('T', [[id], ['(', nt('E'), ')']])]).
% LR(0)
grammar(ex2, [prod('A', [[nt('A'), x], [x]])]).
% SLR(1)
grammar(ex3, [prod('A', [[x, nt('A')], [x]])]).
% not SLR(1)
grammar(ex4, [prod('A', [[x, nt('B')], [nt('B'), y], []]), prod('B', [[]])]).
% not SLR(1)
grammar(ex5, [prod('S', [[id], [nt('V'), ':=', nt('E')]]), prod('V', [[id], [id, '[', nt('E'), ']']]), prod('E', [[nt('V')]])]).
% not SLR(1)
grammar(ex6, [prod('A', [[x], [nt('B'), nt('B')]]), prod('B', [[x]])]).
