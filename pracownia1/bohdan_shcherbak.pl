:- module(bohdan_shcherbak, [solve/2]).
% W tym programie klauzuli typu p v ~q v r będę nazywał klauzulami w początkowej postaci, a typu [p,~q,r] klauzulami.
% [] jako klauzula w początkowej postaci zarówno jak i klauzula nie może być spełniona. 

:- op(200, fx, ~).
:- op(500, xfy, v).


solve([], []) :- !.

solve(ClausesBefore, Solution) :-
	\+ member([], ClausesBefore),
	allVarsNoRep(ClausesBefore, Clauses, Vars),
	solutions(Clauses, AlmostSolution, Vars, LeftVars),
	addingLeftVars(AlmostSolution, LeftVars, SolutionNotSorted),
	sort_alfabet(SolutionNotSorted, Solution).


% Przy pomocy tego sortuję elementy w liście z wartościowaniem według zmiennych
% sortowanie przez wybieranie

select_max([], Res, Res).

select_max([(M, X)|T], (Max,_), Res) :-
	M @> Max,!, select_max(T, (M, X), Res).

select_max([(_, _)|T],(Max, Z),Res) :-
	select_max(T, (Max, Z), Res).

select_max([(M, X)|T],Res) :-
	select_max([(M, X)|T],(M, X),Res).


sort_alfabet([], Solution, Solution).

sort_alfabet(SolutionNotSorted, L , Solution) :-
	select_max(SolutionNotSorted, Max), 
	select(Max, SolutionNotSorted, NewSolutionNotSorted),
	sort_alfabet(NewSolutionNotSorted, [Max|L] , Solution).

sort_alfabet(SolutionNotSorted, Solution) :-
	sort_alfabet(SolutionNotSorted, [], Solution).


% dodaje do rozwiązania wartoświowanie zmiennych, którę mogą mieć 
% oba i znaczenie true i false w danym przypadku

addingLeftVars(AlmostSolution, [], AlmostSolution).

addingLeftVars(AlmostSolution, [V1|OtherVars], [(V1, t)|Sol]) :-
	addingLeftVars(AlmostSolution, OtherVars, Sol).

addingLeftVars(AlmostSolution, [V1|OtherVars], [(V1, f)|Sol]) :-
	addingLeftVars(AlmostSolution, OtherVars, Sol).


% solutions/4 to jest serce tego programu. Tu znajdujemy wszystkie wartoświowania.
% W LeftVars po wykonaniu  znajdują się zmienne, które mogą mieć i wartość true i false przy znalezionym rozwiązaniu.

solutions([], [], LeftVars, LeftVars).

solutions([[~H]|T], [(H, f)|T2], Vars, LeftVars) :-
	!, simplify(T, (H, f), Solution),
	\+ member([],Solution),
	select(H, Vars, NVars),
	solutions(Solution,T2, NVars, LeftVars).

solutions([[H]|T],[(H, t)|T2], Vars, LeftVars) :-
	H \= ~ _, !,
	simplify(T, (H, t), Solution),
	\+ member([],Solution),
	select(H, Vars, NVars),
	solutions(Solution,T2, NVars, LeftVars).

solutions([[~H|S]|T], [(H, Z)|T2], Vars, LeftVars) :-
	length(S,L), L >= 1, (Z = f; Z = t),
	simplify([[~H|S]|T], (H, Z), Solution),
	\+ member([],Solution),
	select(H, Vars, NVars),
	solutions(Solution,T2, NVars, LeftVars).

solutions([[H|S]|T], [(H, Z)|T2], Vars, LeftVars) :-
	H \= ~ _, (Z = f; Z = t),
	length(S,L), L >= 1,
	simplify([[H|S]|T], (H, Z), Solution),
	\+ member([],Solution),
	select(H, Vars, NVars),
	solutions(Solution,T2, NVars, LeftVars).


% Nadaję wartościowanie pewnej zmiennej listy klauzul
% żeby uprościć go do listy klauzul z mniejszą ilością zmiennych

simplify([], (_, t), []).

simplify([], (_, f), []).

simplify([H|T], (X, t), [Res|Tail]) :-
	select(~X, H, Res), !,
	simplify(T, (X, t), Tail).

simplify([H|T], (X, t), Res) :-
	member(X, H), !,
	simplify(T, (X, t), Res).

simplify([H|T], (X, f), [Res|Tail]) :-
	select(X, H, Res), !,
	simplify(T, (X, f), Tail).

simplify([H|T], (X, f), Res) :-
	member(~X, H), !,
	simplify(T, (X, f), Res).

simplify([H|T], (X, f), [H|Res]) :-
	simplify(T, (X, f), Res).

simplify([H|T], (X, t), [H|Res]) :-
	simplify(T, (X, t), Res).


% Wstawia listę z literałami do listy z listami z literałami tak,
% żeby one były posortowane według długośći, a pustą listę
% pomijamy, bo ona oznacza spełnioną klauzulę już na tym poziomie pracy z klauzulami (tak sobie postanowiłem)

insertClause([], X, X).

insertClause(X, [], [X]).

insertClause(X, [H|T], [X,H|T]) :-
	length(X, Lx), length(H, Lh),
	Lx =< Lh, !.

insertClause(X, [H|T], [H|Res]) :-
	insertClause(X, T, Res).	


% Usuwa z listy zmiennych powtórzenia

allVarsNoRep([H|T], Clauses, Vars) :-
	allVarsRep([H|T], Clauses, M),
	no_repeat(M, Vars).


% Przekształca listę z klauzulami w początkowej postaci do 
% listy klauzul, a także pozwala otrzymać zmienne, zawarte w niej

allVarsRep([], [], []).

allVarsRep([H|T], Clauses,  Vars) :-
	H \= [],
	vars(H, Cl, X),
	no_repeat(Cl, Clause),
	allVarsRep(T, Clauses1,  Vars1),
	insertClause(Clause, Clauses1, Clauses),
	append(Vars1, X, Vars).


% Przekształca klauzulę w początkowej postaci do listy z literałami (klauzuli)
% vars(~p v q , [~p, q], [p, q])
% vars(Clause, ListClause, Vars)

vars(~X v Y, [~X|T1], [X|T2]) :-
	!, vars(Y, T1, T2).

vars(X v Y,[X|T1], [X|T2]) :-
	X \= _ v _, !,
	vars(Y,T1, T2).

vars(~Z,[~Z], [Z]) :- !.

vars(Z, [Z], [Z]).


% Usuwa z klauzuli powtarzające się elementy,
% a jeśli klauzula ma zmienną i jej zaprzeczenie, 
% "zwraca" listę pustą, bo taka klauzula jest automatycznie spełniona

no_repeat([],A, A) :- !.

no_repeat([~H|_], A, []) :-
	member(H,A), !.

no_repeat([H|_], A, []) :-
	member(~H,A), !.

no_repeat([H|T],A, Y) :-
	\+ member(H, A), !,
	no_repeat(T, [H|A], Y).

no_repeat([H|T], A, Y) :-
	member(H, A),
	no_repeat(T, A, Y).

no_repeat([H|T], Res) :-
	no_repeat([H|T],[], Res).
