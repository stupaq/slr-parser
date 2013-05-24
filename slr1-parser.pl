% JPP; zadanie 3; Mateusz Machalica; 305678

%% Algebraic types
% prod(Nonterminal, RhsList)
% item(ProductionNonterminal, ProductionRhs, DotPosition)
% ident(ProductionNonterminal, ProductionRhs)
% state(ItemsSetKernel, StateId)
% graph(States, Transitions)
% slr1(Actions)
% action(SourceId, Symbol, ShiftOrReduceOrGoto)
% shift(StateId)
% goto(StateId)
% reduce(Nonterminal, ProductionRhs)
% accept
% follow(Nonterminal, TerminalsSet)

:- use_module(library(lists)).

% printAutomaton(+Grammar, +States, +Actions) : PRED
printAutomaton(_, [], []).
printAutomaton(Grammar, [state(Kernel, Id) | _], _) :-
  closure(Grammar, Kernel, Closure),
  write(state(Closure, Id)), nl,
  fail.
printAutomaton(Grammar, [_ | Rest], Trans) :-
  printAutomaton(Grammar, Rest, Trans).
printAutomaton(_, [], [Trans | _]) :-
  write(Trans), nl,
  fail.
printAutomaton(Grammar, [], [_ | Trans]) :-
  printAutomaton(Grammar, [], Trans).

% createSLR1(+Grammar, -Automaton, -Info) : DET
createSLR1(Original, Automaton, Info) :-
  augment(Original, Grammar),
  createGraph(Grammar, graph(States, Transitions)),
  follow(Grammar, FollowSets),
  fold(reduceIter, (Grammar, FollowSets), [Transitions | States], Actions),
  print(FollowSets), nl,
  printAutomaton(Grammar, States, Actions), nl,
  (findConflict(Actions, Info) ->
    Automaton = null
  ; Automaton = slr1(Actions),
    Info = ok
  ).
% reduceIter(+(Grammar, FollowSets), +ActionsPart, +State, -Actions) : DET
reduceIter((Grammar, FollowSets), Acc, state(Kernel, SetId), Acc1) :-
  closure(Grammar, Kernel, Closure),
  fold(itemIter, (SetId, FollowSets), [Acc | Closure], Acc1).
% itemIter(+(SetId, FollowSets), +Acc, +Item, -Acc1) : DET
itemIter((SetId, FollowSets), Acc, item(N, Rhs, Dot), Acc1) :-
  length(Rhs, Dot),
  member(follow(N, Follow), FollowSets),
  fold(followIter, action(SetId, null, reduce(N, Rhs)), [Acc | Follow], Acc1).
% followIter(+Action, +Acc, +Symbol, +Acc1) : DET
followIter(action(SetId, _, Reduction), Acc, Symbol, [X | Acc]) :-
  Symbol \= nt('Z'),
  X = action(SetId, Symbol, Reduction),
  \+ member(X, Acc).
% findConflict(+Transitions, -Info) : NDET
findConflict(Transitions, konflikt(['conflicting actions: ', Act1, Act2])) :-
  member(action(SrcId, Symbol, Act1), Transitions),
  member(action(SrcId, Symbol, Act2), Transitions),
  Act1 \= Act2.

% augment(+Original, -Augmented) : DET
augment([prod(S, Rhs) | Rest], [prod('Z', [[nt(S), '#']]), prod(S, Rhs) | Rest]).

% createGraph(+Grammar, -AutomatonGraph) : DET
createGraph(Grammar, Graph) :-
  [prod('Z', [Rhs]) | _] = Grammar,
  Kernel = [item('Z', Rhs, 0)],
  Initial = state(Kernel, 0),
  createGraph(Grammar, [Initial], graph([Initial], []), Graph).
% createGraph(+Grammar, +TodoStates, +Acc, -Graph) : DET
createGraph(_, [], Graph, Graph).
createGraph(Grammar, [state(Kernel, Id) | Todo], Graph, Result) :-
  closure(Grammar, Kernel, Closure),
  symbols(Closure, Symbols),
  fold(createTrans, (Closure, Id), [(Todo, Graph) | Symbols], (Todo1, Graph1)),
  createGraph(Grammar, Todo1, Graph1, Result).
% createTrans(+(SrcClosure, SrcId), +(TodoStates, Graph), +Symbol,
%     +(TodoStates, Graph))
createTrans((SrcClosure, SrcId), (Todo, graph(States, Transitions)),
    Symbol, (Todo1, graph(States1, Transitions1))) :-
  transition(SrcClosure, Symbol, DstKernel),
  DstKernel \= [],
  (member(state(DstKernel, DstId), States) ->
    Todo1 = Todo,
    States1 = States
  ; length(States, DstId),
    Todo1 = [state(DstKernel, DstId) | Todo],
    States1 = [state(DstKernel, DstId) | States]
  ),
  (Symbol = nt(_) ->
    Trans = action(SrcId, Symbol, goto(DstId))
  ; Trans = action(SrcId, Symbol, shift(DstId))
  ),
  \+ member(Trans, Transitions),
  Transitions1 = [Trans | Transitions].

% symbols(+Set, -Symbols) : DET
symbols(Items, Symbols) :-
  symbols(Items, [], Symbols).
% symbols(+Items, +Acc, -Symbols) : DET
symbols([], Symbols, Symbols).
symbols([item(N, NRhs, _) | Rest], Acc, Symbols) :-
  append([[nt(N) | NRhs], Acc], Temp),
  remove_dups(Temp, Acc1),
  symbols(Rest, Acc1, Symbols).

% transition(+SourceClosure, +Symbol, -DestinationKernel) : DET
transition(Source, Symbol, Destination) :-
  fold(transitionIter, Symbol, [[] | Source], Destination).
% transitionIter(+Symbol, +KernelPart, +Item, -KernelPart1) : DET
transitionIter(Symbol, Acc, item(N, NRhs, NDot), [X | Acc]) :-
  append_length([Symbol | _], NRhs, NDot),
  XDot is NDot + 1,
  X = item(N, NRhs, XDot),
  \+ member(X, Acc).

% closure(+Grammar, +Set, -SetClosure) : DET
closure(Grammar, Set, Closure) :-
  closure(Set, Grammar, Set, Closure).
% closure(+Todo, +Grammar, +Set, -SetClosure) : DET
closure([], _, Closure, Closure).
closure([Item | Todo], Grammar, Set, Closure) :-
  (closureIter(Grammar, Set, Item, Set1) ->
    closure([Item | Set1], Grammar, Set1, Closure)
  ; closure(Todo, Grammar, Set, Closure)
  ).
% closureIter(+Grammar, +ClosurePart, +Item, -ClosurePart1) : NDET
closureIter(Grammar, Acc, item(_, Rhs, Dot), [X | Acc]) :-
  append_length([nt(N) | _], Rhs, Dot),
  rule(Grammar, nt(N), NRhs), % NDET
  X = item(N, NRhs, 0),
  \+ member(X, Acc).

% accept(+Automaton, +Word)
accept(Automaton, Word) :-
  append([Word, ['#']], Word1),
  accept(Automaton, [0], Word1).
% accept(+Automaton, +Stack, +Word)
accept(slr1(Actions), Stack, [A | Rest]) :-
  [StateId | _] = Stack,
  member(action(StateId, A, shift(DstId)), Actions),
  accept(slr1(Actions), [(DstId, A) | Stack], Rest).
accept(slr1(Actions), Stack, [A | Rest]) :-
  [StateId | _] = Stack,
  member(action(StateId, A, reduce(N, Rhs)), Actions),
  length(Rhs, RhsLen),
  append_length(Stack1, Stack, RhsLen),
  [TempId | _] = Stack1,
  member(action(TempId, nt(N), goto(DstId)), Actions),
  accept(slr1(Actions), [DstId | Stack1], [A | Rest]).
accept(slr1(Actions), [(StateId, _) | _], [A | _]) :-
  member(action(StateId, A, accept), Actions).
% could not find an action, do not backtrack as this is deterministic
accept(_, _, _) :- !, fail. % FIXME

% FIXME rewrite to fix/4 or similar mechanism
% follow(+Grammar, -FollowSets)
follow(Grammar, Set) :-
  setof(follow(N, NSet), follow(Grammar, nt(N), NSet), Set). % FIXME

% follow(+Grammar, +Nonterminal, -FollowSet)
follow(Grammar, nt(N), Set) :-
  setof(X, follow(Grammar, nt(N), X, []), Set). % FIXME
follow(Grammar, nt(N), []) :-
  nonterminal(Grammar, nt(N)),
  \+ follow(Grammar, nt(N), _, []).
% follow(+Grammar, +Nonterminal, +Terminal, +Guard)
follow(Grammar, nt(N), T, Guard) :-
  terminal(Grammar, T),
  rule(Grammar, nt(_), Rhs, Id),
  \+ member(Id, Guard),
  append([_, [nt(N)], B], Rhs),
  first(Grammar, B, T).
follow(Grammar, nt(N), T, Guard) :-
  terminal(Grammar, T),
  rule(Grammar, nt(X), Rhs, Id),
  \+ member(Id, Guard),
  append([_, [nt(N)], B], Rhs),
  nullable(Grammar, B),
  follow(Grammar, nt(X), T, [Id | Guard]).

% first(+Grammar, +SententialForm, +Terminal)
first(Grammar, Sentence, T) :-
  first(Grammar, Sentence, T, []).
% first(+Grammar, +SententialForm, +Terminal, +Guard)
first(_, [T | _], T, _).
first(Grammar, [nt(N) | _], T, Guard) :-
  rule(Grammar, nt(N), Rhs, Id),
  \+ member(Id, Guard), % first(Rhs, T) :- first(Rhs, T), ...
  first(Grammar, Rhs, T, [Id | Guard]).
first(Grammar, Sentence, T, Guard) :-
  append([A, B], Sentence),
  \+ A = [],
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
  \+ intersect(Rhs, [N | Guard]), % nullable(A) :- nullable(A), ...
  nullable(Grammar, Rhs, [N | Guard]).

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
% FIXME end

%% Helpers
% intersect(+List1, +List2) : PRED
intersect(List1, List2) :-
  member(X, List1),
  member(X, List2).

% fold(:Predicate(+Config, +Accumulator, +Elem, -Result), +Config,
%     +[Accumulator | List], -Result) : DET
fold(_, _, [Result], Result).
fold(Fun, Config, [Acc , Elem | Rest], Result) :-
  (call(Fun, Config, Acc, Elem, Acc1) ->
    fold(Fun, Config, [Acc1 | Rest], Result)
  ; fold(Fun, Config, [Acc | Rest], Result)).

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
