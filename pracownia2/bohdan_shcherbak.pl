:- module(bohdan_shcherbak, [resolve/4, prove/2]).

%
% Ten program w razie spełnialności zbioru klauzul znajduje wszystkie rezolwenty wszystkisz rezolwent które można było wyprowadzić 
% z początkowego zbioru klauzul. 
% Program nie jest najwydajniejszy :.(. 
% Nazwy predykatów mowią za siebie, Opowiem trochę o nie bardzo oczywistych z nich.
%
% vars 
% przekształcam klauzulę na listę list jej pozytywnych i negatywnych literałów. 
%
% clausesToLists 
% zmienia formę klauzul dla wygodnej pracy z nimi.
%
% heartResToEnd 
% znajduje dowód sprzeczności (nie najkrótrzy) lub jesli go nie ma i zbiór jest spełnialny zawodzi.
%
% clauseAndSet 
% znajduje wszystkie resolwenty między klauzulą i każdą klauzulą z zadanego zbioru.
%
% filterDuplicates 
% usuwa z tych rezolwent te które byłe gdzieś wcześniej. sqClauseRes znajduje którąś rezolwentę między dwoma klauzulami lub zawodzi 
% jeśli tych rezolwent jest dwie, bo to znaczy, że każda z nich jest tautologią. 
%
% resolveLists
% znajduje rezolwente względem zadanej zmiennej. 
%
% qAlfabetSort i mergeAlf 
% są przeznaczone do zachowania porządku alfabetycznego w klauzulach, żeby ich można było porównywać z większą łatwością.
%

:- op(200, fx, ~).
:- op(500, xfy, v).

resolve(Var, Clause1, Clause2, ResClause) :-
	vars1(Clause1, [Cl1Pos, Cl1Neg]),
	vars1(Clause2, [Cl2Pos, Cl2Neg]), 
	select(Var, Cl1Pos, Cl1PosRes), 
	select(~Var, Cl2Neg, Cl2NegRes), 
	append(Cl1PosRes, Cl2Pos, ClAlmResPos), 
	append(Cl1Neg, Cl2NegRes, ClAlmResNeg),
	no_repeat(ClAlmResPos, ClResPos),
	no_repeat(ClAlmResNeg, ClResNeg),
	listToClause([ClResPos, ClResNeg], ResClause).

vars1(Clause, [T1,T2]) :-
	vars1(Clause, T1before, T2before),
	no_repeat(T1before, T1), 
	no_repeat(T2before, T2).
vars1(~X v Y, T1, [~X|T2]) :-
	!, vars1(Y, T1, T2).
vars1(X v Y, [X|T1], T2) :-
	X \= _ v _, !,
	vars1(Y,T1, T2).
vars1(~Z,[], [~Z]) :- !.
vars1(Z, [Z], []).

no_repeat([],_, R-R) :- !.
no_repeat([H|T],A, NR-R) :-
	\+ member(H, A), !,
	append2([H|Y]-Y, Help-W, NR-R),
	no_repeat(T, [H|A], Help-W).
no_repeat([_|T], A, NR-R) :-
	no_repeat(T, A, NR-R).
no_repeat([], []).
no_repeat([H|T], Res) :-
	no_repeat([H|T],[], Res-[]).


listToClause([[],[]], []).
listToClause([[E], []], E) :- !.
listToClause([[], [E]], E) :- !.
listToClause([[], [HN|TN]], HN v Z) :-
	listToClause([[], TN], Z).
listToClause([[HP|TP], C], HP v Z) :-
	listToClause([TP, C], Z).

vars(Clause, [T1,T2]) :-
	vars(Clause, [], [], T1, T2),
	\+ (T1 = [], T2 = []),!.
vars(~X v _, Pos, _, [], []) :-
	member(X, Pos), !.
vars(~X v Y, Pos, Neg, PosRes, NegRes) :-
	member(~X, Neg),!,
	vars(Y, Pos, Neg, PosRes, NegRes).
vars(~X v Y, Pos, Neg, PosRes, NegRes) :- !,
	vars(Y, Pos, [~X|Neg], PosRes, NegRes).
vars(X v _, _, Neg, [], []) :-
	X \= _ v _, member(~X, Neg), !.
vars(X v Y, Pos, Neg, PosRes, NegRes) :-
	X \= _ v _, member(X, Pos),!,
	vars(Y, Pos, Neg, PosRes, NegRes).
vars(X v Y, Pos, Neg, PosRes, NegRes) :-
	!,
	vars(Y, [X|Pos], Neg, PosRes, NegRes).
vars(~Z, Pos, _, [], []) :-
	member(Z, Pos),!.
vars(~Z, Pos, Neg, Pos, Neg) :- 
	member(~Z, Neg),!.
vars(~Z, Pos, Neg, Pos, [~Z|Neg]) :- !.
vars(Z, _, Neg, [], []) :-
	member(~Z, Neg),!.
vars(Z, Pos, Neg, Pos, Neg) :-
	member(Z, Pos),!.
vars(Z, Pos, Neg, [Z|Pos], Neg).

prove(Clauses, [([], axiom)]) :-
	hasEmptyClause(Clauses), !.
prove(Clauses, _) :-
	length(Clauses, 1), !, false.
prove(Clauses, Proof) :-
	clausesToLists(Clauses, ClList, 1, Naxiom),
	ClList = [HClList|TClList],
	open(TClList, OTClList-End),
	heartResToEnd(OTClList-End, [HClList|Y]-Y, Naxiom, Resolvents-R, _, _),
	R = [],
	revFindPath(Resolvents, AlmProof),
	final(AlmProof, Proof, 1, []),!.

final([],[], _, _).
final([HA|TA], [HB|TB], Num, Replasements) :-
	listToClause2(HA, HB, Num,  Replasement, Replasements),
	NewNum is Num + 1,
	final(TA, TB, NewNum, [Replasement|Replasements]).


listToClause2([Pos, Neg, N, axiom], (Cl, axiom), Num, N/Num, _) :-
	listToClause([Pos, Neg], Cl).

listToClause2([Pos, Neg, N, (Zm, O1, O2)], (Cl, (Zm, NewO1, NewO2)), Num, N/Num, Replasements) :-
	listToClause([Pos, Neg], Cl),
	replace(O1, Replasements, NewO1),
	replace(O2, Replasements, NewO2).

replace(Num, [Num/X|_], X) :-!.
replace(Num, [_|T], RNum) :-
	replace(Num, T, RNum).	

open([], X-X).
open([H|T], [H|TOp]-End) :-
	open(T, TOp-End).

append2(X-Y,Y-Z,X-Z).

hasEmptyClause([[]|_]) :- !.
hasEmptyClause([_|T]) :-
	hasEmptyClause(T).

revFindPath(Resolvents, AlmProof) :-
	revFindPath(Resolvents, [], AlmProof).
revFindPath([[[], [], N, Or]|_], Rev, AlmProof) :-
	path(N, [[[], [], N, Or]|Rev], AlmProof-[]).


revFindPath([HR|TR], Rev, AlmProof) :-
	revFindPath(TR, [HR|Rev], AlmProof).

path(N, [[Pos, Neg, W, axiom]|_], [[Pos, Neg, W, axiom]|Y]-Y) :- 
	N = W, !.
path(N, [[Pos, Neg, N, (Z, O1, O2)]|T], Path-P) :-
	!,
	path(O1, T, PathO1-PO1),
	path(O2, T, PathO2-PO2),
	append2(PathO2-PO2, [[Pos, Neg, N, (Z, O1, O2)]|Y]-Y, NewPathO2-NewPO2),
	append2(PathO1-PO1, NewPathO2-NewPO2, Path-P).
path(N, [_|T], Path-P) :-
	path(N, T, Path-P).

heartResToEnd(X-X, Resolvents-R, Nyet, Resolvents-R, Nyet, 0) :-
	var(X), !, false.
heartResToEnd(X-X, Resolvents-R, Nyet, Resolvents-R, Nyet, 1) :-
	var(X),!.
heartResToEnd([HToCheck|TToCheck]-TC, Checked-CH, Nbefore, Resolvents-R, Nyet, Found) :-
	clauseAndSet(HToCheck, Checked-CH, Res-R,  Nbefore, Nafter, Found),
	filterDuplicates(Res-R, [HToCheck|TToCheck]-TC, Checked-CH, Filtered-FD), 
	append2(Checked-CH, [HToCheck|Y]-Y, NewChecked-NewCH),
	append2(TToCheck-TC, Filtered-FD, NewToCheck-NTC),
	heartResToEnd(NewToCheck-NTC, NewChecked-NewCH, Nafter, Resolvents-R, Nyet, Found).

filterDuplicates(R, _, _, X-X)  :- var(R), !.

filterDuplicates([HToFilter|TToFilter], ToCheck-TC, Checked-CH, Filtered-FD) :-
	\+(memberDiff(HToFilter, ToCheck-TC); memberDiff(HToFilter, Checked-CH)),!,
	append2([HToFilter|Y]-Y, Help-W, Filtered-FD),
	filterDuplicates(TToFilter, ToCheck-TC, Checked-CH, Help-W).

filterDuplicates([_|TToFilter], ToCheck-TC, Checked-CH, Filtered-FD) :-
	filterDuplicates(TToFilter, ToCheck-TC, Checked-CH, Filtered-FD).
	
filterDuplicates(C-_, ToCheck-TC, Checked-CH, Filtered-FD) :-
	filterDuplicates(C, ToCheck-TC, Checked-CH, Filtered-FD).



memberDiff(_, [H|_]-_) :- var(H), !, false.
memberDiff(_, H-_) :- var(H), !, false.
memberDiff([P, N, _, _], [[P, N, _, _]|_]-_) :- !.
memberDiff(Clause, [H|T]-Z) :-
	\+ var(H),
	memberDiff(Clause, T-Z).

clauseAndSet(Clause, [H|T]-_, Res-R,  Nbefore, Nafter, Found) :-
	\+ oneVariableClause(Clause),!,
	notOneVarClauseAndSet(Clause, [H|T], Res-R,  Nbefore, Nafter, Found).
clauseAndSet(Clause, [H|T]-_, Res-R,  Nbefore, Nafter, Found) :- !,
	oneVarClauseAndSet(Clause, [H|T], Res-R,  Nbefore, Nafter, Found).

oneVariableClause([[], [_], _,_]).
oneVariableClause([[_], [], _,_]).

oneVarClauseAndSet(_, H, Y-Y,  Nafter, Nafter, _) :- 
	var(H),
	 !.
oneVarClauseAndSet(Clause, [H|_], Res-R,  Nbefore, Nafter, Found) :-
	sqClauseRes(Clause, H, Nbefore, Resolvent), 
	found(Resolvent),%!, 
	Found = 1,
	Nafter is Nbefore + 1,
	Res-R = [Resolvent|Y]-Y.
oneVarClauseAndSet(Clause, [H|T], Res-R,  Nbefore, Nafter, Found) :-
	sqClauseRes(Clause, H, Nbefore, Resolvent), !,
	append2([Resolvent|Y]-Y, Help-W, Res-R),
	Nnext is Nbefore + 1,
	oneVarClauseAndSet(Clause, T, Help-W,  Nnext, Nafter, Found).
oneVarClauseAndSet(Clause, [_|T], Res-R, Nbefore, Nafter, Found) :-
	oneVarClauseAndSet(Clause, T, Res-R,  Nbefore, Nafter, Found).

notOneVarClauseAndSet(_, H, Y-Y,  Nafter, Nafter, _) :- 
	var(H),
	!.
notOneVarClauseAndSet(Clause, [H|T], Res-R,  Nbefore, Nafter, Found) :-
	sqClauseRes(Clause, H, Nbefore, Resolvent), !,
	append2([Resolvent|Y]-Y, Help-W, Res-R),
	Nnext is Nbefore + 1,
	notOneVarClauseAndSet(Clause, T, Help-W,  Nnext, Nafter, Found).
notOneVarClauseAndSet(Clause, [_|T], Res-R, Nbefore, Nafter, Found) :-
	notOneVarClauseAndSet(Clause, T, Res-R,  Nbefore, Nafter, Found).

found([[],[],_,_]).

sqClauseRes(Clause1, Clause2, Nbefore, [Pos, Neg, N, Origin]) :-
	sqClauseRes(Clause1, Clause1, Clause2, Nbefore, [PosBefore, NegBefore, N, Origin]),
	no_repeat(PosBefore, Pos), no_repeat(NegBefore, Neg),!.
sqClauseRes([[], [], _, _], _, _, _, [[],[],X,Y]) :- var(X), var(Y), !, false.
sqClauseRes([[], [], _, _], _, _, _, Resolvent) :- var(Resolvent),!, false.
sqClauseRes([[], [], _, _], _, _, _, _).
sqClauseRes([[], [H1Neg|T1Neg], _, _], Clause1, Clause2, N, Resolvent) :-
	resolveLists(H1Neg, Clause1, Clause2, N, Res), !, 
	Res = Resolvent, 
	sqClauseRes([[], T1Neg, _, _], Clause1, Clause2, N, Resolvent).
sqClauseRes([[], [_|T1Neg], _, _], Clause1, Clause2, N, Resolvent) :-
	sqClauseRes([[], T1Neg, _, _], Clause1, Clause2, N, Resolvent).
sqClauseRes([[H1Pos|T1Pos], Cl1Neg, _, _], Clause1, Clause2, N, Resolvent) :-
	resolveLists(H1Pos, Clause1, Clause2, N, Res),!, 
	Res = Resolvent, 
	sqClauseRes([T1Pos, Cl1Neg, _, _], Clause1, Clause2, N, Resolvent).
sqClauseRes([[_|T1Pos], Cl1Neg, _, _], Clause1, Clause2, N, Resolvent) :-
	sqClauseRes([T1Pos, Cl1Neg, _, _], Clause1, Clause2, N, Resolvent).

resolveLists(~Var, [Cl1Pos, Cl1Neg, N1, _], [Cl2Pos, Cl2Neg, N2, _], NNew, [ClResPos, ClResNeg, NNew, (Var, N2, N1)]) :-
	select(Var, Cl2Pos, Cl2PosRes), 
	select(~Var, Cl1Neg, Cl1NegRes), !, 
	mergeAlf(Cl2PosRes, Cl1Pos, ClResPos),
	mergeAlf(Cl2Neg, Cl1NegRes, ClResNeg).

resolveLists(Var, [Cl1Pos, Cl1Neg, N1, _], [Cl2Pos, Cl2Neg, N2, _], NNew, [ClResPos, ClResNeg, NNew, (Var, N1, N2)]) :-
	select(Var, Cl1Pos, Cl1PosRes), 
	select(~Var, Cl2Neg, Cl2NegRes), 
	mergeAlf(Cl1PosRes, Cl2Pos, ClResPos), 
	mergeAlf(Cl1Neg, Cl2NegRes, ClResNeg).


clausesToLists([], [], Naxiom, Naxiom).
clausesToLists([H|T], Reshaped, N, Naxiom) :-
	member(H,T), !, 
	clausesToLists(T, Reshaped, N, Naxiom).
clausesToLists([H|T], Reshaped, N, Naxiom) :- 
	(vars(H, Hn) ->	
		(
			addNumberAxiomSort(Hn, N, Hch), 
			Reshaped = [Hch|Tch], 
			N1 is N + 1, 
			clausesToLists(T, Tch, N1, Naxiom)
		)
	);
	clausesToLists(T, Reshaped, N, Naxiom).

addNumberAxiomSort([PosBefore, NegBefore], N, [PosAfter, NegAfter, N, axiom]) :-
	qAlfabetSort(PosBefore,[], PosAfter),
	qAlfabetSort(NegBefore,[], NegAfter).

split([], _, [], []).
split([H|T], Med, Small, [H|Big]) :-
	H @>= Med, !, split(T, Med, Small, Big).
split([H|T], Med, [H|Small], Big) :-
	split(T, Med, Small, Big).

qAlfabetSort([], X, X).
qAlfabetSort([H|T], X, R) :-
	split(T, H, S, B),
	qAlfabetSort(B, X, B1),
	qAlfabetSort(S, [H|B1], R).

mergeAlf([], H, H) :- !.
mergeAlf(H, [], H) :- !.
mergeAlf([H1|T1],[H2|T2], [H1|Tail]) :-
	H1 @< H2,!, mergeAlf(T1, [H2|T2], Tail).
mergeAlf([H1|T1],[H2|T2], [H2|Tail]) :-
	mergeAlf([H1|T1], T2, Tail).
