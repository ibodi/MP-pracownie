:- module(bohdan_shcherbak_eval, [run/5]).
/*
Przedstawiam Państwu kolejne zadanie. Tu generalnie są przepisane reguły i może dopisane swoje, ponieważ niektórych reguł 
nie wystarczało tekich jak reguła ewaluacji pary czy reguła obliczenia pary.

Przepraszam bardzo za to, że ten program jest nie zbyt czytelny. 

Jak zawszę koło miejsc, gdzie moim zdaniem nie jest oczywiste co ten czy inny predykat robi, napisałem krótki opis.

Niestety nie zrozumiałem po co uzywać DCG do generowania list klauzul. Dlatego tego nie robiłem.

Po programie umieściłem w komentarzu inną jesgo wersje z wyjątkami predykatu throw. Po raz pierwszy używam predykatu throw i dlatego sobie eksperymentuje.
Fajnie się udaje. 
*/

:- op(200, fx, ~).
:- op(500, xfy, v).

run(Program, FName, Arg, Value, Clauses) :-
 	eval(Program,[],call(_, FName, Arg),Value, Clauses).

eval(_,_,Num,Num, []) :- integer(Num),!.

eval(_,_,num(_,Num),Num, []).

eval(_,_,empty(_),[], []).

eval(_,Env,var(_,Name),Value, []) :-
	member((var(_,Name),Value),Env), !;
	var(Value).

eval(_,_,[H|T],[H|T], []).

eval(_,_,[],[], []).

eval(_,_,(P,K),(P,K), []).

eval(Prog,Env,bit(_, E),[X], SdE) :-
	eval(Prog,Env,E,1,SdE1),!,
	gensym(wire,X), SdE = [X|SdE1];
	eval(Prog,Env,E,0,SdE0),!,
	gensym(wire,X), SdE = [~X|SdE0].

eval(Prog,Env,bitsel(_, E1, E2),[Nth], SdE) :-
	eval(Prog,Env,E1,Sygnals, SdE1), 
	eval(Prog,Env,E2,Num, SdE2),integer(Num),
	nth(Num, Sygnals, Nth),!,
	join(SdE1, SdE2, SdE).

eval(Prog,Env,bitsel(_, E1, E2, E3),N3toN2, SdE) :-
	eval(Prog,Env,E1,Sygnals, SdE1),
	eval(Prog,Env,E2,Num2, SdE2),integer(Num2),
	eval(Prog,Env,E3,Num3, SdE3),integer(Num3),
	fromAtoB(Num3, Num2, Sygnals, N3toN2),!,
	join(SdE1, SdE2, Help),
	join(SdE3, Help, SdE).

eval(Prog,Env,op(_, '~', E1),Sygnals, SdE) :-
	eval(Prog,Env,E1,Sygnals1, SdE1),
	length(Sygnals1,L1), 
	(
		createNSygs(L1,Sygnals),
		addNotSdE(Sygnals1,Sygnals, SdE2),!,
		join(SdE2, SdE1, SdE)
	).

eval(Prog,Env,op(_, '@', E1, E2),Sygnals, SdE) :-
	eval(Prog,Env,E1,Sygnals1, SdE1),
	eval(Prog,Env,E2,Sygnals2, SdE2),
	join(SdE2, SdE1, SdE),
	(
		\+ (Sygnals1 = [_|_]; Sygnals1 = []) -> throw("@: "/E1/" evaluates to "/Sygnals1/" which is not a vector");
		append(Sygnals2,Sygnals1, Sygnals),!
	).

eval(Prog,Env,op(_, '#', E),N, SdE) :-
	eval(Prog,Env,E,Sygnals, SdE),  % Nie ma dodatkowych efektów ubocznych
	length(Sygnals,N),!.

eval(Prog,Env,op(_, Op, E1, E2),N, SdE) :-
	member(Op, ['+','-','*','/','%']),
	eval(Prog,Env,E1,N1, SdE1),integer(N1),
	eval(Prog,Env,E2,N2, SdE2),integer(N2),
	join(SdE2, SdE1, SdE),
	(
		Op = '%' ,!,N is N1 mod N2;
		Op = '/' ,!, N is N1 // N2;
		Expr =.. [Op,N1,N2],N is Expr
	),!.

eval(Prog,Env,op(_, '-', E),N, SdE) :-
	eval(Prog,Env,E,N1, SdE),integer(N1),
	N is - N1,!.

eval(Prog,Env,op(_, Op, E1, E2),N, SdE) :-
	member(Op, ['<=','>=','=','<>','<','>']),
	eval(Prog,Env,E1,N1, SdE1),integer(N1),
	eval(Prog,Env,E2,N2, SdE2),integer(N2),
	join(SdE2, SdE1, SdE),
	(
		(
			Op = '<>' -> N1 \= N2;
			Op = '<=' -> N1 =< N2;
			Expr =.. [Op,N1,N2], Expr
		), N = 1;
		N = 0
	),!.


eval(Prog,Env,op(_, Op, E1, E2),Sygnals, SdE) :-
	member(Op, ['&','|','^']),
		eval(Prog,Env,E1,Sygnals1, SdE1),
		eval(Prog,Env,E2,Sygnals2, SdE2),
		length(Sygnals1,L1),
		length(Sygnals2,L2),
		L1 = L2,
		createNSygs(L1,Sygnals),
		addSdE(Op,Sygnals1,Sygnals2,Sygnals, SdE3),
		join(SdE2, SdE1, Help),
		join(SdE3, Help, SdE),!.

eval(Prog,Env,if(_, E1, E2, E3),Value, SdE) :-
	eval(Prog,Env,E1,N1, SdE1), integer(N1),
	(
		N1 = 0 -> eval(Prog,Env,E3,Value, SdE2);
		eval(Prog,Env,E2,Value, SdE2)
	),
	join(SdE2, SdE1, SdE),!.

eval(Prog,Env,let(_, P, E1, E2),Value, SdE) :-
	eval(Prog,Env,E1,Value1, SdE1),
	assEnvChange(Env, P, Value1, NewEnv),
	eval(Prog,NewEnv,E2,Value, SdE2),
	join(SdE1,SdE2,SdE),!.

eval(Prog,Env,pair(_, E1, E2),(Value1, Value2), SdE) :-
	eval(Prog,Env,E1,Value1, SdE1),
	eval(Prog,Env,E2,Value2, SdE2),
	join(SdE1,SdE2,SdE),!.

eval(Prog,Env,call(_, Name, E1),Value, SdE) :-
	member(def(Name,Model,Expr), Prog),
	eval(Prog,Env,E1,Value1,SdE1),
	assEnvChange(Env, Model, Value1, NewEnv),
	eval(Prog,NewEnv,Expr,Value,SdE2),
	join(SdE1,SdE2,SdE),!.

% Tu się odbywa zmiana środowiska przy przypisaniu 
assEnvChange(Env, Var, Value, NewEnv) :-
	Var = pair(_,Var1,Var2), Value = (Value1, Value2),!,
		assEnvChange(Env, Var1, Value1, NewEnv1),
		assEnvChange(NewEnv1, Var2, Value2, NewEnv);
	(
		functor(Value,Functor,Arity),
			Functor \= '[|]', Functor \= [], Functor \= (','), 
			\+ integer(Functor);
		var(Value);
		Var = pair(_,Var1,Var2)
	),!,false;
	Var = wildcard(_),!, NewEnv = Env;
	select((Var, Val), Env, EnvA),!,
	(
		Val = Value,!, NewEnv = Env;
		(
			Value = num(_,Num),!,NewEnv = [(Var, Num)|EnvA];
			NewEnv = [(Var,Value)|EnvA]
		)
	);
	(
		Value = num(_,Num),!,NewEnv = [(Var,Num)|Env];
		NewEnv = [(Var, Value)|Env]
	).

% Prawie append (nie uwzględnia kolejność)
join([], A, A).
join([H|T], A, W) :-
  join(T, [H|A], W).

and(B,C,A,[A v ~B v ~C, ~A v B, ~A v C]).
or(B,C,A,[~A v B v C,A v ~B, A v ~C]).
xor(B,C,A,[~A v ~B v ~C, ~A v B v C, A v ~B v C, A v B v ~C]).
not(B,A,[~A v ~B, A v B]).

% Zwraca n-ty element listy Sygnals
nth(N, Sygnals, Nth) :-
	N >= 0,!, nthH(N, Sygnals, Nth).
nthH(0, [H|_], H) :- !,true.
nthH(N, [_|Ss], Nth) :-
	N1 is N - 1,
	nthH(N1, Ss, Nth).

% Pozwala wziąć wszystkie elementy listy od indeksu A do B
fromAtoB(A, B, List, AtoB) :-
	A >=0, B >= A,!,fromAtoBH(A, B, List, AtoB).
fromAtoBH(0, 0, [H|_], [H]) :- !.
fromAtoBH(0, B, [H|T], [H|T2]):-
	B1 is B - 1, 
	fromAtoBH(0, B1, T, T2).
fromAtoBH(A, B, [_|T], AtoB) :-
	A1 is A - 1,B1 is B - 1,
	fromAtoBH(A1, B1, T, AtoB).


% Koduje bramki AND, OR czy XOR międzi sygnałami z lewej i prawej listy
addSdE(_,[],[],[],[]).
addSdE(Op,[S1|S1s],[S2|S2s],[S|Ss], SdE3):-
	(
		Op = '&', and(S1,S2,S,SdEs);
		Op = '|', or(S1,S2,S,SdEs);
		Op = '^', xor(S1,S2,S,SdEs)
	),
	join(SdEs,Help,SdE3),
	addSdE(Op,S1s,S2s,Ss, Help),!.

% Koduje bramki NOT międzi sygnałami z lewej i prawej listy
addNotSdE([],[],[]).
addNotSdE([S1|S1s],[S|Ss], SdE2) :-
	not(S1,S,SdEs),
	join(SdEs,Help,SdE2),
	addNotSdE(S1s,Ss, Help).

% Utwarza n świeżych sygnałów
createNSygs(0,[]):-!.
createNSygs(N,[X|T]) :-
	gensym(wire,X),
	N1 is N - 1,
	createNSygs(N1,T).



/*

Moja wersja z throw (bardziej interesująca ale  trochę nie odpowiada wymaganiom zadania)

run(Program, FName, Arg, Value, Clauses) :-
 	eval(Program,[],call(_, FName, Arg),Value, Clauses).

eval(_,_,Num,Num, []) :- integer(Num),!.

eval(_,_,num(_,Num),Num, []).

eval(_,_,empty(_),[], []).

eval(_,Env,var(_,Name),Value, []) :-
	member((var(_,Name),Value),Env), !;
	var(Value),throw("var: variable "/Name/" is not in the environment "/Env).

eval(_,_,[H|T],[H|T], []).

eval(_,_,[],[], []).

eval(_,_,(P,K),(P,K), []).

eval(Prog,Env,bit(_, E),[X], SdE) :-
	catch(eval(Prog,Env,E,1,SdE1),Catch,throw("bit: "/Catch)),!,
	gensym(wire,X), SdE = [X|SdE1];
	catch(eval(Prog,Env,E,0,SdE0),Catch,throw("bit: "/Catch)),!,
	gensym(wire,X), SdE = [~X|SdE0];
	throw("bit: "/E/" doesn't evaluate to zero or to one").

eval(Prog,Env,bitsel(_, E1, E2),[Nth], SdE) :-
	catch(eval(Prog,Env,E1,Sygnals, SdE1),Catch,throw("bitsel/2: "/Catch)), 
	catch(eval(Prog,Env,E2,Num, SdE2),Catch,throw("bitsel/2: "/Catch)),integer(Num),
	(	
		catch(nth(Num, Sygnals, Nth),Catch,throw("bitsel/2: "/Num/Sygnals/Catch)),!,
		join(SdE1, SdE2, SdE)
	);throw("bitsel/2: "/E2/" doesn't evaluate to integer").

eval(Prog,Env,bitsel(_, E1, E2, E3),N3toN2, SdE) :-
	catch(eval(Prog,Env,E1,Sygnals, SdE1),Catch,throw("bitsel/3: "/Catch)),
	catch(eval(Prog,Env,E2,Num2, SdE2),Catch,throw("bitsel/3: "/Catch)),integer(Num2),
	(
		catch(eval(Prog,Env,E3,Num3, SdE3),Catch,throw("bitsel/3: "/Catch)),integer(Num3),
		(
			catch(fromAtoB(Num3, Num2, Sygnals, N3toN2),Catch,throw("bitsel/3: "/Catch)),!,
			join(SdE1, SdE2, Help),
			join(SdE3, Help, SdE)
		);throw("bitsel/3: "/E3/" doesn't evaluate to integer")
	);throw("bitsel/3: "/E2/" doesn't evaluate to integer").

eval(Prog,Env,op(_, '~', E1),Sygnals, SdE) :-
	catch(eval(Prog,Env,E1,Sygnals1, SdE1),Catch,throw("~: "/Catch)),
	catch(length(Sygnals1,L1),Catch,throw("~: "/Catch)), 
	(
		createNSygs(L1,Sygnals),
		addNotSdE(Sygnals1,Sygnals, SdE2),!,
		join(SdE2, SdE1, SdE)
	).

eval(Prog,Env,op(_, '@', E1, E2),Sygnals, SdE) :-
	catch(eval(Prog,Env,E1,Sygnals1, SdE1),Catch,throw("@: "/Catch)),
	catch(eval(Prog,Env,E2,Sygnals2, SdE2),Catch,throw("@: "/Catch)),
	join(SdE2, SdE1, SdE),
	(
		\+ (Sygnals1 = [_|_]; Sygnals1 = []) -> throw("@: "/E1/" evaluates to "/Sygnals1/" which is not a vector");
		append(Sygnals2,Sygnals1, Sygnals),!
	);throw("@: "/E2/" evaluates to "/Sygnals2/" which is not a vector").

eval(Prog,Env,op(_, '#', E),N, SdE) :-
	catch(eval(Prog,Env,E,Sygnals, SdE),Catch,throw("#: "/Catch)),  % Nie ma dodatkowych efektów ubocznych
	catch(length(Sygnals,N),Catch,throw("#: "/Catch)),!.

eval(Prog,Env,op(_, Op, E1, E2),N, SdE) :-
	member(Op, ['+','-','*','/','%']),
	(
		catch(eval(Prog,Env,E1,N1, SdE1),Catch,throw(Op/": "/Catch)),integer(N1),
		(	
			catch(eval(Prog,Env,E2,N2, SdE2),Catch,throw(Op/": "/Catch)),integer(N2),
			(
				join(SdE2, SdE1, SdE),
				(
					Op = '%' ,!,N is N1 mod N2;
					Op = '/' ,!, N is N1 // N2;
					Expr =.. [Op,N1,N2],N is Expr
				),!
			);throw(Op/"2: "/E2/" doesn't evaluate to integer")
		);throw(Op/"2: "/E1/" doesn't evaluate to integer")
	).

eval(Prog,Env,op(_, '-', E),N, SdE) :-
	catch(eval(Prog,Env,E,N1, SdE),Catch,throw("-: "/Catch)),integer(N1),
	N is - N1,!;
	throw("-: "/E/" does not evaluate to integer").

eval(Prog,Env,op(_, Op, E1, E2),N, SdE) :-
	member(Op, ['<=','>=','=','<>','<','>']),
	(
		catch(eval(Prog,Env,E1,N1, SdE1),Catch,throw(Op/": "/Catch)),integer(N1),
		(
			catch(eval(Prog,Env,E2,N2, SdE2),Catch,throw(Op/": "/Catch)),integer(N2),
			(
				join(SdE2, SdE1, SdE),
				(
					(
						Op = '<>' -> N1 \= N2;
						Op = '<=' -> N1 =< N2;
						Expr =.. [Op,N1,N2], Expr
					), N = 1;
					N = 0
				),!
			);throw(Op/"2: "/E2/" doesn't evaluate to integer")
		);throw(Op/"2: "/E1/" doesn't evaluate to integer")
	).

eval(Prog,Env,op(_, Op, E1, E2),Sygnals, SdE) :-
	member(Op, ['&','|','^']),
	eval(Prog,Env,E1,Sygnals1, SdE1),Catch,throw(Op/": "/Catch)),
	eval(Prog,Env,E2,Sygnals2, SdE2),Catch,throw(Op/": "/Catch)),
	catch(length(Sygnals1,L1),Catch,throw(Op/": "/Catch)),
	catch(length(Sygnals2,L2),Catch,throw(Op/": "/Catch)), 
	L1 = L2,
	createNSygs(L1,Sygnals),
	addSdE(Op,Sygnals1,Sygnals2,Sygnals, SdE3),
	join(SdE2, SdE1, Help),
	join(SdE3, Help, SdE),!.

eval(Prog,Env,if(_, E1, E2, E3),Value, SdE) :-
	catch(eval(Prog,Env,E1,N1, SdE1),Catch,throw("if: "/Catch)), integer(N1),
	N1 = 0 -> catch(eval(Prog,Env,E3,Value, SdE2),Catch,throw("if: "/Catch));
	catch(eval(Prog,Env,E2,Value, SdE2),Catch,throw("if: "/Catch))
	,join(SdE2, SdE1, SdE),!.

eval(Prog,Env,let(_, P, E1, E2),Value, SdE) :-
	catch(eval(Prog,Env,E1,Value1, SdE1),Catch,throw("let: "/Let/Catch)),
	catch(assEnvChange(Env, P, Value1, NewEnv),Catch,throw("let: "/Let/Catch)),
	catch(eval(Prog,NewEnv,E2,Value, SdE2),Catch,throw("let: "/Let/Catch)),
	join(SdE1,SdE2,SdE),!.

eval(Prog,Env,pair(_, E1, E2),(Value1, Value2), SdE) :-
	catch(eval(Prog,Env,E1,Value1, SdE1),Catch,throw("pair: "/Catch)),
	catch(eval(Prog,Env,E2,Value2, SdE2),Catch,throw("pair: "/Catch)),
	join(SdE1,SdE2,SdE),!.

eval(Prog,Env,call(_, Name, E1),Value, SdE) :-
	member(def(Name,Model,Expr), Prog),
	(
		catch(eval(Prog,Env,E1,Value1,SdE1),Catch,throw("call: "/Catch)),
		catch(assEnvChange(Env, Model, Value1, NewEnv),Catch,throw("call: "/Catch)),
		catch(eval(Prog,NewEnv,Expr,Value,SdE2),Catch,throw("call: "/Catch)),
		join(SdE1,SdE2,SdE),!
	);throw("call: there is no such function as "/Name).

% Tu się odbywa zmiana środowiska przy przypisaniu 
assEnvChange(Env, Var, Value, NewEnv) :-
	Var = pair(_,Var1,Var2), Value = (Value1, Value2),!,
		assEnvChange(Env, Var1, Value1, NewEnv1),
		assEnvChange(NewEnv1, Var2, Value2, NewEnv);
	Var = pair(_,Var1,Var2),!,
		throw("EnvironChange: Can't assign "/pair(_,Var1,Var2)/" to "/Value);
	(
		functor(Value,Functor,Arity),
			Functor \= '[|]', Functor \= [], Functor \= (','), 
			\+ integer(Functor);
		var(Value)
	),!, throw("EnvironChange: Can't assign "/Var/" to inappropriate value "/Value);
	Var = wildcard(_),!, NewEnv = Env;
	select((Var, Val), Env, EnvA),!,
	(
		Val = Value,!, NewEnv = Env;
		(
			Value = num(_,Num),!,NewEnv = [(Var, Num)|EnvA];
			NewEnv = [(Var,Value)|EnvA]
		)
	);
	(
		Value = num(_,Num),!,NewEnv = [(Var,Num)|Env];
		NewEnv = [(Var, Value)|Env]
	).

% Prawie append (nie uwzględnia kolejność)
join([], A, A).
join([H|T], A, W) :-
  join(T, [H|A], W).

and(B,C,A,[A v ~B v ~C, ~A v B, ~A v C]).
or(B,C,A,[~A v B v C,A v ~B, A v ~C]).
xor(B,C,A,[~A v ~B v ~C, ~A v B v C, A v ~B v C, A v B v ~C]).
not(B,A,[~A v ~B, A v B]).

% Zwraca n-ty element listy Sygnals
nth(N, Sygnals, Nth) :-
	N >= 0,!, nthH(N, Sygnals, Nth);
	throw("nth: "/N/" is not natural number").
nthH(0, [H|_], H) :- !,true.
nthH(N, [_|Ss], Nth) :-
	N1 is N - 1,
	nthH(N1, Ss, Nth).
nthH(_, [], _) :- throw("nth: list of sygnals is too short").
nthH(_, Sygnals, _) :- throw("nth: "/Sygnals/" is not a vector").

% Pozwala wziąć wszystkie elementy listy od indeksu A do B
fromAtoB(A, B, List, AtoB) :-
	A >=0, B >= A,!,fromAtoBH(A, B, List, AtoB)
	;throw("fromAtoB: "/A/" and "/B/" are inappropriate indexes of a beginning and end of subvector").
fromAtoBH(0, 0, [H|_], [H]) :- !.
fromAtoBH(0, B, [H|T], [H|T2]):-
	B1 is B - 1, 
	fromAtoBH(0, B1, T, T2).
fromAtoBH(A, B, [_|T], AtoB) :-
	A1 is A - 1,B1 is B - 1,
	fromAtoBH(A1, B1, T, AtoB).
fromAtoBH(_, _, [], _) :- throw("fromAtoB: vector is too short").
fromAtoBH(_,_,Sygnals,_) :- throw("fromAtoB: "/Sygnals/" is not a vector").

% Poniżej są predykaty raczej nie odnoszące się do zadania

stringRun(StrProg, FName, Arg, Value, Clauses):-
	stringParse_(StrProg,Program),
	run(Program, FName, Arg, Value, Clauses).

identity(StrProg, NewStrProg) :-
	stringParse_(StrProg,Program),
	unparse(Program, NewStrProg),!.

unparse(V,"_"):- var(V),!.

unparse(Num, String) :-
	integer(Num),
	atom_string(Num, String),!.

unparse((L,P),String) :- 
	\+ var(L), \+ var(P), 
	unparse(L,UnL),
	unparse(P,UnP),
	string_concat(UnL,",",Beg1),
	string_concat(Beg1,UnP,String),!.

unparseProg([H|T],String) :-
	unparse(H,UnH),
	unparse(T,UnT),
	string_concat(UnH,"\n",Beg1),
	string_concat(Beg1,UnT,String),!.

unparse(def(Name,Model,Expr),String) :-
	D = "def ",
	atom_string(Name,UnName),
	string_concat(D,UnName,De),
	string_concat(De,"(",Def),
	unparse(Model,Mod),
	unparse(Expr, Exp),
	string_concat(Def,Mod,DefMod),
	string_concat(DefMod,") = ",Alm),
	string_concat(Alm,Exp,String),!.

unparse(pair(_,A,B),String):-
	unparse(A,UnA),
	unparse(B,UnB),
	string_concat(UnA, ", ",Alm),
	string_concat(Alm, UnB, String),!.

unparse(var(_,Name),UnName):-
	atom_string(Name,UnName),!.

unparse(num(_,Num),String) :-
	atom_string(Num,String),!.

unparse([],"[]") :-!.

unparse([H|T],String) :-
	atomic_list_concat([H|T], ',', Atom), atom_string(Atom, Alm1),
	string_concat("[",Alm1,Alm),
	string_concat(Alm,"]",String),!.

unparse(wildcard(_),"_") :-!.

unparse(if(_, E1, E2, E3),String):-
	If = "if ",Then = " then ", Else = " else ",
	unparse(E1,UnE1),unparse(E2,UnE2),unparse(E3,UnE3),
	string_concat(If,UnE1,Beg),
	string_concat(Beg,Then,Beg2),
	string_concat(Beg2,UnE2,Beg3),
	string_concat(Beg3,Else,Beg4),
	string_concat(Beg4,UnE3,String),!.

unparse(let(_, E1, E2, E3),String):-
	Let = "let ",Eq = " = ", In = " in ",
	unparse(E1,UnE1),unparse(E2,UnE2),unparse(E3,UnE3),
	string_concat(Let,UnE1,Beg),
	string_concat(Beg,Eq,Beg2),
	string_concat(Beg2,UnE2,Beg3),
	string_concat(Beg3,In,Beg4),
	string_concat(Beg4,UnE3,String),!.

unparse(op(_, Op, E),String):-
	atom_string(Op,UnOp),
	unparse(E,UnE),
	string_concat(UnOp,UnE,String),!.

unparse(op(_, Op, E1, E2),String):-
	atom_string(Op,UnOp),
	unparse(E1,UnE1),unparse(E2,UnE2),
	string_concat(UnE1,UnOp,Alm),
	string_concat(Alm,UnE2,String),!.

unparse(bitsel(_, E1, E2),String):-
	unparse(E1,UnE1),unparse(E2,UnE2),
	string_concat(UnE1,"[",Beg1),
	string_concat(Beg1,UnE2,Beg2),
	string_concat(Beg2,"]",String),!.

unparse(bitsel(_, E1, E2, E3),String):-
	unparse(E1,UnE1),unparse(E2,UnE2),unparse(E3,UnE3),
	string_concat(UnE1,"[",Beg1),
	string_concat(Beg1,UnE2,Beg2),
	string_concat(Beg2,"..",Beg3),
	string_concat(Beg3,UnE3,Beg4),
	string_concat(Beg4,"]",String),!.

unparse(call(_, Name, E),String):-
	atom_string(Name,UnName),
	unparse(E,UnE),
	string_concat(UnName,"(",Beg1),
	string_concat(Beg1, UnE,Beg2),
	string_concat(Beg2, ")",String),!.

unparse(empty(_),"[]") :-!.

unparse(bit(_,E),String):-
	unparse(E,UnE),
	string_concat("[",UnE,Beg1),
	string_concat(Beg1,"]",String),!.
*/