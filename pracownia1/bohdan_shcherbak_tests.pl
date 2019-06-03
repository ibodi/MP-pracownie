:- module(bohdan_shcherbak_tests, [tests/5]).

:- op(200, fx, ~).
:- op(500, xfy, v).

tests(excluded_middle1, validity, [p v ~p], 500, solution([(p,t)])).
tests(excluded_middle2, validity, [p v ~p], 500, count(2)).
tests(empty_closure, validity, [[]], 500, count(0)).
tests(empty_set, validity, [], 500, count(1)).
tests(first1, validity, [a v b, a v b v ~c, b v a v ~b v ~c, c], 500, count(3)).
tests(first2, validity, [a v b, a v b v ~c, b v a v ~b v ~c, c], 500, solution([(a, t),  (b, f),  (c, t)])).
tests(first3, validity, [a v b, a v b v ~c, b v a v ~b v ~c, c], 500, solution([(a, t),  (b, t),  (c, t)])).
tests(first4, validity, [a v b, a v b v ~c, b v a v ~b v ~c, c], 500, solution([(a, f),  (b, t),  (c, t)])).
tests(second1, validity, [a v b v ~c, ~d v e v f, c v d, b], 500, solution( [(a, t),  (b, t),  (c, t),  (d, t),  (e, f),  (f, t)])).
tests(second2, validity, [a v b v ~c, ~d v e v f, c v d, b], 500, count(20)).
tests(third1, validity, [x v ~y v z, x v ~y v ~z, ~x v ~y v z], 500, solution([(x, t),  (y, f),  (z, t)])).
tests(third2, performance, [x v ~y v z, x v ~y v ~z, ~x v ~y v z], 500, count(5)).
tests(fourth, performance, [p v q v r, ~r v ~q v ~p, ~q v r, ~r v p], 500, count(2)).
tests(fifth, validity, [p v r, ~r v ~s, q v s, q v r, ~p v ~q, s v p], 500, count(0)).
tests(sixth, performance, [b v ~b, a v t v ~i, i v ~i v a v t], 500, count(14)).
tests(seventh, validity, [b v ~b v a v c], 500, count(8)).
tests(eight1, performance, [a v b v c, a v b v ~c, a v ~b v ~c, a v ~b v c], 500, count(4)).
tests(eight2, validity, [a v b v c, a v b v ~c, a v ~b v ~c, a v ~b v c], 500, solution([(a, t),  (b, f),  (c, f)])).
tests(eight2, validity, [a v b v c, a v b v ~c, a v ~b v ~c, a v ~b v c], 500, solution([(a, t),  (b, t),  (c, f)])).
tests(nineth, performance, [a], 500, count(1)).
tests(tenth, validity, [a v b, a v b v ~c, b v a v ~b v ~c, c, [], x v ~y v ~z, a v t v ~i], 500, count(0)).
tests(eleventh1, validity, [b v ~c v a v c v d, ~d v ~a v c, d v ~c v b, d v ~e, e v d v ~a], 500, count(15)).
tests(eleventh2, validity, [b v ~c v a v c v d, ~d v ~a v c, d v ~c v b, d v ~e, e v d v ~a], 500, solution([(a, f),  (b, f),  (c, f),  (d, t),  (e, t)])).
tests(eleventh3, validity, [b v ~c v a v c v d, ~d v ~a v c, d v ~c v b, d v ~e, e v d v ~a], 500, solution([(a, f),  (b, t),  (c, f),  (d, f),  (e, f)])).
tests(eleventh4, validity, [b v ~c v a v c v d, ~d v ~a v c, d v ~c v b, d v ~e, e v d v ~a], 500, solution([(a, f),  (b, f),  (c, t),  (d, t),  (e, t)])).
tests(twelveth, performance,[a v b v ~t v y v ~i, i v o v ~b v ~y v a v m , ~m v y v i v ~t v b v ~a v g, ~a v ~b v t v ~y v i v ~m, a v ~b v i v ~i v ~o v o, k v p v ~u v ~i v o v ~e v q] , 2000, solution([(a,f),(b,t),(e,t),(g,f),(i,f),(k,t),(m,f),(o,f),(p,f),(q,t),(t,f),(u,f),(y,f)])).
tests(thirteenth, performance, [b v ~n v o v p v ~y v r v w v p v ~i v o v ~r v q, m v ~b v s v e v q v ~c v p v ~t v u v r v ~d v l, a v m v ~p v ~i v ~z v ~y v i, [], a v ~a ], 500, count(0)).