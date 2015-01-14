:- module(completion).
:- set_prolog_flag(optimise, true).
:- use_module(library(terms)).
:- use_module(library(apply_macros)).
:- use_module(library(lists)).

%% YAP only.
undefined(A) :- format('Undefined predicate: ~w~n',[A]), fail.
:- unknown(U,undefined(X)).

is_var(X) :- var(X), !.
is_var('$VAR'(_)).

%% Size of terms.
size(X, 1) :- is_var(X), !.
size(X, N) :-
    X =.. [_F|Xs],
    maplist(size, Xs, Ys),
    sum_list(Ys, M),
    N is M+1.

%% Knuth-Bendix ordering.
try_orient(X, Y, Res) :- orient(X, Y, Res), !.
try_orient(_, _, incomparable).

orient(Res, X, Y) :- orient_local(Res, X, Y), vars_check(Res, X, Y).

vars_check('<', X, Y) :- vars_contained(X, Y).
vars_check('>', X, Y) :- vars_contained(Y, X).
vars_check('=', _, _).

vars_contained(X, Y) :- sorted_vars(X, Xs), sorted_vars(Y, Ys), subsequence(Xs, Ys).
sorted_vars(X, Xs) :- vars(X, Xs1), sort(Xs1, Xs).
vars(X, Xs) :- vars(X, [], Xs).
vars(X, Vs, Vs1) :- is_var(X), !, Vs1 = [X|Vs].
vars(X, Vs, Vs1) :- X =.. [_|Xs], vars_list(Xs, Vs, Vs1).
vars_list([], Vs, Vs).
vars_list([X|Xs], Vs, Vs2) :- vars(X, Vs, Vs1), vars_list(Xs, Vs1, Vs2).

orient_local(Res, X, Y) :- X == Y, !, Res = '='.
orient_local(_,   X, Y) :- is_var(X), is_var(Y), !, fail.
orient_local(Res, X, Y) :- is_var(X), !, vars_contained(X, Y), Res = '<'.
orient_local(Res, X, Y) :- is_var(Y), !, vars_contained(Y, X), Res = '>'.
orient_local(Res, X, Y) :- size(X, M), size(Y, N), M \= N, !, compare(Res, M, N).
orient_local(Res, X, Y) :- X =.. [_|Xs], Y =.. [_|Ys], length(Xs, M), length(Ys, N), M \= N, !, compare(Res, M, N).
orient_local(Res, X, Y) :- X =.. [F|_],  Y =.. [G|_],  F \= G, !, compare(Res, F, G).
orient_local(Res, X, Y) :- X =.. [F|Xs], Y =.. [F|Ys], orient_list(Res, Xs, Ys).

orient_list('=', [], []).
orient_list(Res, [X|Xs], [Y|Ys]) :- (orient_local(Res, X, Y), !); orient_list(Res, Xs, Ys).

subsequence([], _) :- !.
subsequence([X|Xs], [X|Ys]) :- !, subsequence(Xs, Ys).
subsequence(Xs, [_|Ys]) :- subsequence(Xs, Ys).

%% Rules.
:- dynamic(rule/2).

write_rules :-
    forall(rule(L, R), (write_rule(rule(L, R)), nl)).

write_rule(rule(L, R)) :-
    number(0, _, rule(L, R)),
    write(L), write(' -> '), write(R),
    fail.
write_rule(rule(L, R)).

number(N, N1, X) :- var(X), !, X = N, N1 is N+1.
number(N, N1, X) :- X =.. [_|Xs], number_list(N, N1, Xs).
number_list(N, N, []).
number_list(N, N2, [X|Xs]) :- number(N, N1, X), number_list(N1, N2, Xs).

reduce(X, Y) :- reduce(rule, X, Y).
reduce(_, X, _) :- var(X), !, fail.
reduce(P, X, Y) :- call(P, X, Y), acyclic_term(X).
reduce(P, X, Y) :- X =.. [F|Xs], reduce_list(P, Xs, Ys), Y =.. [F|Ys].
reduce_list(P, [X|Xs], [Y|Xs]) :- reduce(P, X, Y).
reduce_list(P, [X|Xs], [X|Ys]) :- reduce_list(P, Xs, Ys).

%% reduce(rule(L, R), X, Y) reduces only wrt rule(L, R).
rule(L, R, L, R).

normalise_ground(X, Y) :- reduce(X, Z), !, normalise_ground(Z, Y).
normalise_ground(X, X).

normalise(X, Y) :-
    skolemise(Ctx, X, X1),
    normalise_ground(X1, Y1),
    unskolemise(Ctx, Y1, Y).

skolemise(Ctx, X, Y) :-
    copy_term(X, Y),
    numbervars(Y, 1, N),
    length(Xs, N),
    Ctx =.. [f|Xs],
    unskolemise(Ctx, Y, X).

unskolemise(Ctx, '$VAR'(N), X) :- !, arg(N, Ctx, X).
unskolemise(_, X, Y) :- var(X), !, X=Y.
unskolemise(Ctx, X, Y) :- X =.. [F|Xs], maplist(unskolemise(Ctx), Xs, Ys), Y =.. [F|Ys].

%% The queue of facts.
:- dynamic(queue/3).

next_fact(L, R) :-
    queue(_, _, _), !,
    next_fact_from(0, L, R).
next_fact_from(N, L, R) :-
    (clause(queue(N, L, R), true, Ref), !, erase(Ref));
    (M is N+1, next_fact_from(M, L, R)).

enqueue(L, R) :-
    normalise(L, L1), normalise(R, R1),
    rule_size(rule(L1, R1), Size),
    ignore((
    L1 \== R1,
    skolemise(_, (L1 = R1), (LS = RS)),
    not(queue(Size, LS, RS)),
    assertz(queue(Size, L1, R1)))).

rule_size(rule(L, R), Size) :-
    %size(L, M), size(R, N), Size is M+N.
    size(L, Size).

%% Critical pairs.
critical_pair(rule(L, R), L1, R) :- reduce(L, L1).
critical_pair(rule(L, R), L1, R1) :- reduce(rule(L, R), L1, R1).

%% The loop (TM)
loop :-
    next_fact(L, R),
    consider(L, R),
    !,
    loop.
loop.

consider(L, R) :-
    normalise(L, L1),
    normalise(R, R1),
    orient(Res, L1, R1),
    !,
    consider(Res, L1, R1).
consider(L, R) :-
    normalise(L, L1),
    normalise(R, R1),
    writeln(unorientable(L1, R1)).
consider('=', _, _).
consider('<', R, L) :- add_rule(rule(L, R)).
consider('>', L, R) :- add_rule(rule(L, R)).

add_rule(Rule) :-
    rule_size(Rule, Size),
    Size =< 10,
    write(Size), write(' '), write_rule(Rule), nl,
    interreduce(Rule, Reduced),
    assertz(Rule),
    maplist(retract_rule, Reduced),
    maplist(replace_rule, Reduced),
    enqueue_critical_pairs(Rule).
enqueue_critical_pairs(Rule) :-
    critical_pair(Rule, L, R), enqueue(L, R), fail.
enqueue_critical_pairs(_).

interreduce(Rule, Reduced) :-
    findall(Res, (clause(rule(L, R), true, Ref), interreduce(Rule, L, R, Ref, Res)), Reduced).

interreduce(Rule, L, R, Ref, Res) :-
    Rule = rule(RuleL, _),
    not(subsumes_term(L, RuleL)), !,
    skolemise(_, L, L1),
    reduce(Rule, L1, _),
    write('reducing lhs of '), write_rule(rule(L, R)), write(' by '), write_rule(Rule), nl,
    Res = reorient(Ref, L, R).
interreduce(Rule, L, R, Ref, Res) :-
    skolemise(_, R, R1),
    reduce(Rule, R1, _), !,
    write('reducing rhs of '), write_rule(rule(L, R)), write(' by '), write_rule(Rule), nl,
    Res = update(Ref, L, R).
interreduce(_, _, _, _, ok).

retract_rule(reorient(Ref, _, _)) :- erase(Ref).
retract_rule(update(Ref, _, _)) :- erase(Ref).
retract_rule(ok).

replace_rule(reorient(_, L, R)) :- enqueue(L, R).
replace_rule(update(_, L, R)) :-
    normalise(L, L1),
    normalise(R, R1),
    (L1 == R1 -> true; assertz(rule(L1, R1))).
replace_rule(ok).

%% Testing.
%% :- enqueue('<>'('<>'(A,B),C), '<>'(A, '<>'(B, C))).
%% :- enqueue('$$'('$$'(A,B),C), '$$'(A, '$$'(B, C))).
%% :- enqueue('<>'('$$'(A,B),C), '$$'(A, '<>'(B, C))).
%% :- enqueue('<>'(A, nest(_I, B)), '<>'(A, B)).
%% :- enqueue(nest(I, '<>'(A,B)), '<>'(nest(I, A), B)).
%% :- enqueue(nest(I, '$$'(A,B)), '$$'(nest(I,A), nest(I, B))).
%% :- enqueue('<>'(A, empty), A).
%% :- enqueue('<>'(text(S), '$$'('<>'(text(empty), Y), Z)), '$$'(<>(text(S),Y), nest(length(S), Z))).

:- enqueue(plus(zero, X), X).
:- enqueue(plus(minus(X), X), zero).
:- enqueue(plus(plus(X, Y), Z), plus(X, plus(Y, Z))).
:- enqueue(plus(X, Y), plus(Y, X)).
:- loop.
:- write_rules.
:- normalise(plus(plus(c, b), a), X), writeln(X).
