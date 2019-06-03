/*
W związku z tym, że nie widziałem sensu w robieniu tokenów z tekstu w komentarzach 
odrzucam wszystkie znaki wewnątrz komentarzy w lekserze. Przydało mi się częściowo 
to zadanie o poprawnie rozstawionych nawiasach, żeby poradzić sobie z zagnieżdżeniem komentarzy.

Zgrubsza tutaj tylko przepisałem gramatykę tak żeby wyrażenia można było wyprowadzać jednoznacznie.
A także pozbyłem się zapętlenia w miejscu z prostym wyrażeniem i bitami.
*/
:- module(bohdan_shcherbak, [parse/3]).

lexer(Tokens) -->
   white_space,
   (  (  "(*",      !, end_comment(1), { Token = comment }
      ;  ",",       !, { Token = tokComma } % OPERATORY BINARNE
      ;  "<=",      !, { Token = tokLeq }
      ;  ">=",      !, { Token = tokGeq }
      ;  "=",       !, { Token = tokEq }
      ;  "<>",      !, { Token = tokNeq }
      ;  "<",       !, { Token = tokLt }
      ;  ">",       !, { Token = tokGt }
      ;  "^",       !, { Token = tokPow }
      ;  "|",       !, { Token = tokVBar }
      ;  "+",       !, { Token = tokPlus }
      ;  "-",       !, { Token = tokMinus }
      ;  "&",       !, { Token = tokAnd }
      ;  "*",       !, { Token = tokMult }
      ;  "/",       !, { Token = tokDiv }
      ;  "%",       !, { Token = tokMod }
      ;  "@",       !, { Token = tokAt }
      ;  "#",       !, { Token = tokHash } % OPERATORY UNARNE
      ;  "~",       !, { Token = tokTilde }
      ;  "(",       !, { Token = tokOParen } % NAWIASY
      ;  ")",       !, { Token = tokCParen }
      ;  "[",       !, { Token = tokOBrack }
      ;  "]",       !, { Token = tokCBrack }
      ;  "..",       !, { Token = tokDots }
      ;  digit(D),  !,
            number(D, N),
            { Token = tokNumber(N) }
      ;  letter_or_und(L), !, identifier(L, Id),
            {  member((Id, Token), [ (def, tokDef),
                                     (else, tokElse),
                                     (if, tokIf),
                                     (in, tokIn),
                                     (let, tokLet),
                                     (then, tokThen),
                                     ('_', tokUnderscore)]),
               !
            ;  Token = tokId(Id)
            }
      ; [_], { !, false } 
      ), 
      (
          {Token \= comment, !, Tokens = [Token | TokList] }, lexer(TokList);
          lexer(Tokens)
      )
   ;  [], { Tokens = [] }
   ).

% Zjada wszystkie znaki aż do końca komentarza i sprawdza czy komentarze wewnątrz są
% poprawnie ponawiasowane
end_comment(0) --> "(*", !, end_comment(1).
end_comment(0) --> "",!.
end_comment(N) -->
  "*)",!, {N1 is N - 1}, end_comment(N1);
  "(*",!, {N1 is N + 1}, end_comment(N1);  
  [_], end_comment(N).

% Funkcja zmnięszająca męczenie się podczas debugowania
stringLexer(String, Tokens) :-  
  string_to_list(String, List),
  lexer(Tokens, List,[]), write(Tokens).

white_space -->
   [Char], { code_type(Char, space) }, !, white_space.
white_space -->
   [].
   
digit(D) -->
   [D],
      { code_type(D, digit) }.

digits([D|T]) -->
   digit(D),
   !,
   digits(T).
digits([]) -->
   [].

number(D, N) -->
   digits(Ds),
      { number_chars(N, [D|Ds]) }.

% Sprawdza pierwszy znak identyfikatora
letter_or_und(L) -->
   [L], { code_type(L, alpha) };
   [95],{ L = 95 }.               % 95 jest numerem podkreślenia w tablicy ASCII

% Sprawdza czy symbol jest poprawny do użycia w identyfikatorze
csym_or_apost([A|T]) -->
    (
      [A], { code_type(A, csym) };
      [39], { A = 39 }            % 39 jest numerem apostrofa w tablicy ASCII 
    ), !, csym_or_apost(T).

csym_or_apost([]) -->
   [].

identifier(L, Id) -->
   csym_or_apost(As),
      { atom_codes(Id, [L|As]) }.

program(Defs) -->
  definitions(Defs).

definitions([H|T]) -->
  definition(H),
  definitions(T).
definitions([]) --> [].

definition(def(Name, Model, Body)) -->
  [tokDef, tokId(Name),tokOParen],
  model(Model),
  [tokCParen,tokEq],
  expression(Body).

% model to u mnie jest wzorzec (nie chcę szukać jak poprawnie)
simple_model(Model) -->
  (
    [tokOParen], model(Model), [tokCParen]
  );
  (
    [tokUnderscore], {Model = wildcard(no)}
  );
  (
    [tokId(VarName)], {Model = var(no,VarName)}
  ).
  
model(Model) -->
  simple_model(SM), !, opt_model(Model, SM).

opt_model(M, LS) -->
  ([tokComma],!,model(M1), {M = pair(no, LS, M1)})
  ; [], {M = LS}.

% tu na razie przepisane jest z gramatyki
expression(Expr) -->
  (
    [tokIf],!, expression(E1),
    [tokThen], expression(E2),  
    [tokElse], expression(E3),
    { Expr = if(no,E1,E2,E3) }
  );
  (
    [tokLet],!, model(Model), [tokEq],
    expression(E1), [tokIn], expression(E2),
    { Expr = let(no, Model, E1, E2)}
  );
  (
    expression_op(Expr)
  ).

% A tutaj trzeba było pomęczyć się. Przepisałem wszystko tak, żeby była uwzględniona łączność
% oraz prioritety
expression_op(ExprOp) --> exp1(ExprOp).

exp1(E1) -->
  exp2(E2),!,opt_exp1(E2,E1).
opt_exp1(E2,E1) -->
  op1,!,exp1(N1), {E1 = pair(no, E2, N1)}
  ;[],{E1=E2}.

exp2(E2) -->
  exp3(E3_1),!, opt_exp2(E3_1, E2).
opt_exp2(E3_1, E2) -->
  op2(Op2),!, exp3(E3_2),
  { E2 = op(no, Op2, E3_1, E3_2) }
  ; [], {E2 = E3_1}.

exp3(E3) -->
  exp4(E4),!,opt_exp3(E4,E3).
opt_exp3(E4,E3) -->
  op3(Op3),!,exp3(N1), 
  {E3 = op(no, Op3, E4, N1)}
  ;[],{E4=E3}.

exp4(E4) -->
  exp5(E5),!, opt_exp4(E5,E4).
opt_exp4(E5,E4) -->
  op4(Op4), !, exp5(S),
  opt_exp4(op(no, Op4, E5,S),E4);
  [], {E4 = E5}.

exp5(E5) -->
  exp6(E6),!, opt_exp5(E6,E5).
opt_exp5(E6,E5) -->
  op5(Op5), !, exp6(S),
  opt_exp5(op(no, Op5, E6,S),E5);
  [], {E5 = E6}.

exp6(E6) -->
  op6(Op6),exp6(E7),{ E6 = op(no, Op6, E7) };
  exp7(E6).

exp7(E7) -->
  simple_expression(E7).


% proste_wyrażenie w ogóle trudno poznać. Połączyłem wybór bitu i bitów w jeden predykat.
% Połączyłem pozostała część w jeden predykat i ciężkim trudem pozbyłem się zapętlenia.
simple_expression(SE) --> 
  non_cycling_part(NCP),!, 
  opt_simple_expression(NCP, SE).
opt_simple_expression(NCP, SE) -->  
  in_brackets_part(NCP, SE1),!,opt_simple_expression(SE1,SE).
opt_simple_expression(NCP, NCP) --> [].

non_cycling_part(NCP) --> 
  [tokOParen], expression(NCP), [tokCParen];
  atomic_expression(NCP).

in_brackets_part(SE, ChBs) -->
    [tokOBrack], expression(E1),bit_variants(ChBs,SE, E1).    
bit_variants(ChBs,SE, E1) -->
    [tokCBrack],!, { ChBs = bitsel(no, SE, E1) };
    [tokDots], expression(E2), [tokCBrack], 
    { ChBs = bitsel(no, SE, E1, E2) }.

atomic_expression(AE) -->
  var_or_func_call(AE);
  integer_literal(AE);
  empty_vector(AE);
  single_bit(AE).

% Połączyłem w jeden predykat wyznaczenie czy jest to wywołanie funkcji czy zmienna.
var_or_func_call(VarCall) -->
   [tokId(Name)], var_func_choice(VarCall, Name).
var_func_choice(VarCall, Name) -->
  [tokOParen],!, expression(Param), [tokCParen], { VarCall = call(no, Name, Param)};
  { VarCall = var(no, Name) }.

integer_literal(num(no,N)) --> [tokNumber(N)].

empty_vector(empty(no)) --> [tokOBrack, tokCBrack].

single_bit(bit(no, E)) --> [tokOBrack], expression(E), [tokCBrack].

op1 --> [tokComma].

op2('=') --> [tokEq],!.
op2('<>') --> [tokNeq],!.
op2('<') --> [tokLt],!.
op2('>') --> [tokGt],!.
op2('<=') --> [tokLeq],!.
op2('>=') --> [tokGeq].

op3('@') --> [tokAt].

op4('|') --> [tokVBar],!.
op4('^') --> [tokPow],!.
op4('+') --> [tokPlus],!.
op4('-') --> [tokMinus].

op5('&') --> [tokAnd],!.
op5('*') --> [tokMult],!.
op5('/') --> [tokDiv],!.
op5('%') --> [tokMod].

op6('-') --> [tokMinus],!.
op6('#') --> [tokHash],!.
op6('~') --> [tokTilde].

% Jeszcze jedna funkcja zmnięszająca męczenie się podczas debugowania
stringParse(String, Absynt) :-
  string_to_list(String,List),
  parse(_,List, Absynt).

% nie uwzględniam ścieżki do pliku
parse(_, CharCodeList, Absynt) :-
   phrase(lexer(TokList), CharCodeList),
   phrase(program(Absynt), TokList).
