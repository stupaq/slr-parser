% JPP; zadanie 3; Mateusz Machalica; 305678

%% General notes
% All predicates marked with DET are deterministic w.r.t. their ouptut
% arguments even when all cuts are removed (therefore all cuts are green and
% SICSTUS can still make its last call optimization).
% All predicates marked with NDET might be nondeterministic for some inputs.
% Predicates which are deterministic and intended to be efficient (accept/2)
% are guarded by green cuts (therefore the automaton will BOTH accept AND
% reject input without backtracking).
% As usage of red cuts is forbidden the only means of determinization are
% copy-pasting or usage of if-else constructs, the latter sounds a bit better
% (after http://sicstus.sics.se/sicstus/docs/3.7.1/html/sicstus_13.html).

%% Algebraic types
% prod(Nonterminal, RhsList)
% item(ProductionNonterminal, ProductionRhs, DotPosition)
% ident(ProductionNonterminal, ProductionRhs)
% state(ItemsSetKernel, StateId)
% graph(States, Transitions)
% slr1(Actions)
% action(SourceId, Symbol, ShiftGotoOrReduce)
% shiftgoto(StateId) % whether this is shift/goto is determined by a Symbol
% reduce(Nonterminal, ProductionRhs)
% accept
% follow(Nonterminal, TerminalsSet)

:- use_module(library(lists)).

% kernelItem(+Item) : PRED
kernelItem(item('Z', _, _)).
kernelItem(item(_, _, Dot)) :- Dot > 0.

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

% createSLR1det(+Grammar, -Automaton, -Info) : DET
% for compatibility reasons, this will work like createSLR1/3 but returns only
% the first conflict when grammar is not SLR1
%createSLR1det(Grammar,Automaton, Info) :-
%  createSLR1(Grammar, Automaton, Info), !. % red cut, this is a dead code

% createSLR1(+Grammar, -Automaton, -Info) : DET if ok, NDET if konflikt(_)
createSLR1(Original, Automaton, Info) :-
  augment(Original, Grammar),
  createGraph(Grammar, graph(States, Transitions)),
  convlist(acceptAction, States, Accepts),
  follow(Original, FollowSets),
  reductions(States, Grammar, FollowSets, [], Reductions),
  append([Transitions, Reductions, Accepts], Temp1),
  remove_dups(Temp1, Actions),
  %print(FollowSets), nl, % DEBUG
  %printAutomaton(Grammar, States, Actions), nl, % DEBUG
  findConflict(Actions, Info), % NDET
  (Info = ok -> Automaton = slr1(Actions); Automaton = null).
% reductions(+TodoStates, +Grammar, +FollowSets, +Acc, -ReduceActions) : DET
reductions([], _, _, Result, Result).
reductions([state(Kernel, Id) | Todo], Grammar, FollowSets, Acc, Result) :-
  closure(Grammar, Kernel, Closure),
  reductionsIter(Closure, Id, FollowSets, Acc, Acc1),
  reductions(Todo, Grammar, FollowSets, Acc1, Result).
% reductionsIter(+Closure, +SourceId, +FollowSets, +Acc, -Acc1) : DET
reductionsIter([], _, _, Result, Result).
reductionsIter([item(N, Rhs, Dot) | Rest], Id, FollowSets, Acc, Result) :-
  (N \= 'Z', length(Rhs, Dot) ->
    member(follow(N, Follow), FollowSets),
    reductionsFollow(Follow, Id, reduce(N, Rhs), Acc, Acc1)
  ; Acc1 = Acc),
  reductionsIter(Rest, Id, FollowSets, Acc1, Result).
% reductionsFollow(+Follow, +SourceId, +Reduction, +Acc, -Acc1) : DET
reductionsFollow([], _, _, Acc, Acc).
reductionsFollow([Symbol | Rest], SourceId, Reduction, Acc, Result) :-
  X = action(SourceId, Symbol, Reduction),
  (member(X, Acc) -> Acc1 = Acc; Acc1 = [X | Acc]),
  reductionsFollow(Rest, SourceId, Reduction, Acc1, Result).

% findConflict(+Transitions, -Info) : NDET
findConflict(Transitions, konflikt(('conflicting actions: ', Act1, Act2))) :-
  member(action(SrcId, Symbol, Act1), Transitions),
  member(action(SrcId, Symbol, Act2), Transitions),
  Act1 \= Act2.
findConflict(Transitions, ok) :-
  \+ findConflict(Transitions, konflikt(_)).

% augment(+Original, -Augmented) : DET
augment([prod(S, Rhs) | Rest], [prod('Z', [[nt(S), '#']]), prod(S, Rhs) | Rest]).

% acceptAction(+State, -Action) : DET
acceptAction(state(Items, Id), action(Id, '#', accept)) :-
  % item('Z', _, _) is always a kernel item
  member(item('Z', _, 1), Items).

% createGraph(+Grammar, -AutomatonGraph) : DET
createGraph(Grammar, Graph) :-
  [prod('Z', [Rhs]) | _] = Grammar,
  Kernel = [item('Z', Rhs, 0)],
  Initial = state(Kernel, 0),
  createGraph([], [Initial], _, Grammar, graph([Initial], []), Graph).
% createGraph(+TodoSymbols, +TodoStates, +StateClosure, +Grammar, +Acc,
%     -Graph) : DET
createGraph([], [], _, _, Graph, Graph).
createGraph([], [state(Kernel, Id) | Todo], _, Grammar, Graph, Result) :-
  closure(Grammar, Kernel, Closure),
  symbols(Closure, Symbols),
  createGraph(Symbols, Todo, state(Closure, Id), Grammar, Graph, Result).
createGraph([Symbol | Rest], Todo, State, Grammar, Graph, Result) :-
  (createTrans(State, Todo, Graph, Symbol, Todo1, Graph1) -> true
  ; Todo1 = Todo, Graph1 = Graph),
  createGraph(Rest, Todo1, State, Grammar, Graph1, Result).
% createTrans(+ClosureState, +TodoStates, +Graph, +Symbol,
%     -TodoStates1, -Graph1) : DET
createTrans(state(SrcClosure, SrcId), Todo, graph(States, Transitions), Symbol,
    Todo1, graph(States1, [Trans | Transitions])) :-
  % we do not use '#' transitions between states as there is no accepting state
  Symbol \= '#',
  transition(SrcClosure, Symbol, DstKernel),
  DstKernel \= [],
  Trans = action(SrcId, Symbol, shiftgoto(DstId)),
  % if we have this transition then have destination state too
  \+ member(Trans, Transitions),
  (findState(state(DstKernel, DstId), States) -> % DET at most one match
    Todo1 = Todo,
    States1 = States
  ; length(States, DstId),
    Todo1 = [state(DstKernel, DstId) | Todo],
    States1 = [state(DstKernel, DstId) | States]
  ).

% findState(?State, +States) : NDET
findState(state(Kernel, Id), [state(Kernel1, Id) | _]) :-
  setEqual(Kernel, Kernel1).
findState(State, [_ | Rest]) :-
  findState(State, Rest).

% symbols(+Set, -Symbols) : DET
symbols(Set, Symbols) :-
  symbols(Set, [], Temp1),
  remove_dups(Temp1, Symbols).
% symbols(+Items, +Acc, -Symbols) : DET
symbols([], Symbols, Symbols).
symbols([item(N, NRhs, _) | Rest], Acc, Symbols) :-
  append([[nt(N) | NRhs], Acc], Acc1),
  symbols(Rest, Acc1, Symbols).
symbols([prod(N, RhsList) | Rest], Acc, Symbols) :-
  append([[nt(N)], Acc | RhsList], Acc1),
  symbols(Rest, Acc1, Symbols).

% terminals(+Grammar, -Terminals) : DET
terminals(Grammar, Terminals) :-
  symbols(Grammar, Temp1),
  exclude(nonterminal, Temp1, Terminals).

% nonterminals(+Grammar, -Nonterminals) : DET
nonterminals(Grammar, Nonterminals) :-
  symbols(Grammar, Temp1),
  include(nonterminal, Temp1, Nonterminals).

% nonterminal(+Symbol) : PRED
nonterminal(nt(_)).

% transition(+SourceClosure, +Symbol, -DestinationKernel) : DET
transition(Source, Symbol, Destination) :-
  transition(Source, Symbol, [], Kernel),
  normKernel(Kernel, Destination).
% transition(+TodoItems, +Symbol, +Acc, -Result) : DET
transition([], _, Result, Result).
transition([Item | Rest], Symbol, Acc, Result) :-
  transitionOne(Item, Symbol, Acc, NewItem),
  transition(Rest, Symbol, [NewItem | Acc], Result).
transition([Item | Rest], Symbol, Acc, Result) :-
  \+ transitionOne(Item, Symbol, Acc, _),
  transition(Rest, Symbol, Acc, Result).
% transitionOne(+Item, +Symbol, +Acc, -ItemImage) : DET
transitionOne(item(N, NRhs, NDot), Symbol, Acc, X) :-
  append_length([Symbol | _], NRhs, NDot),
  XDot is NDot + 1,
  X = item(N, NRhs, XDot),
  \+ member(X, Acc).

% normKernel(+ItemsSet, -NormalizedKernel) : DET
normKernel(Set, Kernel) :-
  %sort(Set, Temp1), % this is not allowed according to problem statement
  remove_dups(Set, Kernel).

% closure(+Grammar, +Set, -SetClosure) : DET
closure(Grammar, Set, Closure) :-
  closure(Set, Grammar, Set, Closure).
% closure(+Todo, +Grammar, +Set, -SetClosure) : DET
closure([], _, Closure, Closure).
closure([Item | Todo], Grammar, Set, Closure) :-
  (closureIter(Grammar, Set, Item, NewItem) ->
    closure([Item, NewItem | Todo], Grammar, [NewItem | Set], Closure)
  ; closure(Todo, Grammar, Set, Closure)).
% closureIter(+Grammar, +ClosurePart, +Item, -NewItem) : NDET
closureIter(Grammar, Acc, item(_, Rhs, Dot), X) :-
  append_length([nt(N) | _], Rhs, Dot),
  rule(Grammar, nt(N), NRhs), % NDET
  X = item(N, NRhs, 0),
  \+ member(X, Acc).

% accept(+Automaton, +Word) : DET
accept(Automaton, Word) :-
  append([Word, ['#']], Word1),
  accept(Automaton, [0], Word1).
% accept(+Automaton, +Stack, +Word) : DET
accept(slr1(Actions), Stack, [A | Rest]) :-
  [StateId | _] = Stack,
  member(action(StateId, A, shiftgoto(DstId)), Actions), !, % no conflicts
  accept(slr1(Actions), [DstId | Stack], Rest).
accept(slr1(Actions), Stack, [A | Rest]) :-
  [StateId | _] = Stack,
  member(action(StateId, A, reduce(N, Rhs)), Actions), !, % no conflicts
  length(Rhs, RhsLen),
  append_length(Stack1, Stack, RhsLen),
  [TempId | _] = Stack1,
  member(action(TempId, nt(N), shiftgoto(DstId)), Actions), !, % no conflicts
  accept(slr1(Actions), [DstId | Stack1], [A | Rest]).
accept(slr1(Actions), [StateId | _], [A | _]) :-
  member(action(StateId, A, accept), Actions).
accept(_, _, _) :- !, fail. % parser is deterministic

% follow(+Grammar, -FollowSets) : DET
follow(Original, Set) :-
  augment(Original, Grammar),
  nonterminals(Grammar, Nonterminals),
  follow([], Nonterminals, Grammar, [], Temp),
  deaugment(Temp, [], Set).
% follow(+Terminals, +Nonterminals, +Grammar, +Acc, -Result) : DET
follow([], [], _, Result, Result).
follow([], [nt(N) | Rest], Grammar, Acc, Result) :-
  terminals(Grammar, Terminals),
  follow(Terminals, Rest, Grammar, [follow(N, []) | Acc], Result).
follow([T | TRest], NTerms, Grammar, [follow(N, Set) | AccRest], Result) :-
  (followCheck(Grammar, nt(N), T) ->
    Set1 = [T | Set]
  ; Set1 = Set),
  follow(TRest, NTerms, Grammar, [follow(N, Set1) | AccRest], Result).

% deaugment(+AugmentedFollow, +Acc, -FollowSet) : DET
deaugment([], Result, Result).
deaugment([follow('Z', _) | Rest], Acc, Result) :-
  !, % green, clauses are disjoint
  deaugment(Rest, Acc, Result).
deaugment([Follow | Rest], Acc, Result) :-
  follow('Z', _) \= Follow,
  deaugment(Rest, [Follow | Acc], Result).

% We can pass around an accumulator and construct entire set at once (as in
% many predicates before), the problem is that it is not necessarily faster
% (see Visited manipulations) and way less legible.
% followCheck(+Grammar, +Nonterminal, +Terminal) : PRED
followCheck(Grammar, nt(N), Terminal) :-
  followCheck(Grammar, nt(N), [nt(N)], Grammar, Terminal).
% followCheck(+GrammarTodo, +Nonterminal, +Visited, +Grammar, +Terminal) : PRED
followCheck([prod(_, []) | Rest], nt(N), Visited, Original, T) :-
  followCheck(Rest, nt(N), Visited, Original, T).
followCheck([prod(X, [[] | ProdRest]) | Rest], nt(N), Visited, Original, T) :-
  followCheck([prod(X, ProdRest) | Rest], nt(N), Visited, Original, T).
followCheck([prod(X, [[W | RhsRest] | ProdRest]) | Rest], nt(N), Visited, Original, T) :-
  W \= nt(N),
  followCheck([prod(X, [RhsRest | ProdRest]) | Rest], nt(N), Visited, Original, T).
followCheck([prod(X, [[nt(N) | RhsRest] | ProdRest]) | Rest], nt(N), Visited, Original, T) :-
  Todo = [prod(X, [RhsRest | ProdRest]) | Rest],
  (first(Original, RhsRest, T) -> true
  ; (\+ member(nt(X), Visited), nullable(Original, RhsRest) ->
      (followCheck(Original, nt(X), [nt(X) | Visited], Original, T) -> true
      ; % we know that there is no point in calling followCheck for X and T
        followCheck(Todo, nt(N), [nt(X) | Visited], Original, T)
      )
    ; followCheck(Todo, nt(N), Visited, Original, T)
    )
  ).

% first(+Grammar, +SententialForm, +Terminal) : PRED
first(Grammar, Sentence, T) :-
  first(Grammar, Sentence, T, []).
% first(+Grammar, +SententialForm, +Terminal, +Guard) : PRED
first(_, [T | _], T, _).
first(Grammar, [nt(N) | _], T, Guard) :-
  rule(Grammar, nt(N), Rhs),
  \+ member(Rhs, Guard), % first(Rhs, T) :- first(Rhs, T), ...
  first(Grammar, Rhs, T, [Rhs | Guard]).
first(Grammar, Sentence, T, Guard) :-
  append([A, B], Sentence),
  \+ A = [],
  nullable(Grammar, A),
  first(Grammar, B, T, Guard).

% nullable(+Grammar, +SententialForm) : PRED
nullable(Grammar, Sentence) :-
  nullable(Grammar, Sentence, []).
% nullable(+Grammar, +SententialForm, +Guard) : PRED
nullable(_, [], _).
nullable(Grammar, [nt(N) | Rest], Guard) :-
  nullable(Grammar, nt(N), Guard),
  nullable(Grammar, Rest, Guard).
% nullable(+Grammar, +Nonterminal, +Guard) : PRED
nullable(Grammar, nt(N), OldGuard) :-
  rule(Grammar, nt(N), Rhs),
  Guard = [nt(N) | OldGuard],
  \+ intersect(Rhs, Guard), % nullable(A) :- nullable(A), ...
  nullable(Grammar, Rhs, Guard).

% rule(+Grammar, +Nonterminal, -ProductionRhs) : NDET
rule([prod(N, RhsList) | _], nt(N), Rhs) :-
  member(Rhs, RhsList).
rule([_ | Rest], nt(N), Rhs) :-
  rule(Rest, nt(N), Rhs).

%% Helpers
% intersect(+List1, +List2) : PRED
intersect(List1, List2) :-
  member(X, List1),
  member(X, List2).

% subset(+Subset, +Superset) : PRED
subset([], _).
subset([X | Set1], Set2) :-
  member(X, Set2),
  subset(Set1, Set2).

% setEqual(+Set1, +Set2) : PRED
setEqual(Set1, Set2) :-
  subset(Set1, Set2),
  subset(Set2, Set1).

