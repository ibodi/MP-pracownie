:- module(bohdan_shcherbak_tests, [resolve_tests/5, prove_tests/4]).

:- op(200, fx, ~).
:- op(500, xfy, v).

resolve_tests(one_variable_in_one_of_the_clauses, q, q v p v r, ~q, p v r).
resolve_tests(duplicates, s, p v ~r v s v ~t v ~t v p v s, ~s v r v p v ~t, p v r v ~r v ~t).
resolve_tests(random_literals, p, p v y v u v ~i v ~e v o v ~z v p v p, s v b v ~p v t v ~i v e v j, y v u v o v s v b v t v e v j v ~i v ~e v ~z).
resolve_tests(lots_of_rs_at_once_and_empty_clause, r, r v r v r v r v r v r v r v r v r v r, ~r v ~r v ~r v ~r v ~r v ~r v ~r v ~r v ~r v ~r v ~r v ~r, []).
resolve_tests(easy_one, q, q v p, ~q v s, s v p).
resolve_tests(long_one, i, t v b v ~n v y v i v ~o v p v ~w v q v z v ~n v b v c v ~l v ~t v ~n v ~o v ~n v t v b v i v q v f, ~i v o v ~p v ~t v h v ~e v m v ~q v c v ~s v z v ~i, t v b v y v p v q v z v c v f v o v h v m v ~n v ~o v ~w v ~l v ~t v ~p v ~e v ~q v ~s).
resolve_tests(message_from_aliens, y, ~w v ~e v ~c v a v m v ~e v h v e v r v ~e v t v ~o v t v ~a v k v e v ~w v h v ~a v t v ~w v e v n v e v ~e v d v g v ~i v e v ~u v s v ~a v l v ~l v r v ~a v ~b v b v ~i v t v ~s v o v f v ~t v h v ~e v e v ~a v r v ~t v h v ~o v r v y v o v u v ~r v p v ~l v a v n v ~e v t v w v ~i v l v ~l v b v ~e v d v e v ~s v t v r v ~o v y v e v ~d, o v ~h v n v ~o v n v ~o v t v ~r v a v ~b v b v ~i v t v ~s v ~y v o v u v b v u v ~s v t v a v r v d v s, a v m v h v e v r v t v k v n v d v g v s v l v b v o v f v u v p v w v ~w v ~e v ~c v ~o v ~a v ~i v ~u v ~l v ~b v ~s v ~t v ~r v ~d v ~h).

prove_tests(one_clause_in_a set, validity, [b v t v ~u v o], sat).
prove_tests(empty_clause_in_a_set, validity, [a v b, a v b v ~c, b v a v ~b v ~c, c, [], x v ~y v ~z, a v t v ~i], unsat).
prove_tests(empty_set_of_clauses, validity, [], sat).
prove_tests(unsat, validity, [~p v q, p, r v q, ~q, p v q v ~r], unsat).
prove_tests(cant_invent_a_name, validity, [p v q v r, ~r v ~q v ~p, ~q v r, ~r v p], sat).
prove_tests(three_variables, validity, [a v b, a v b v ~c, b v a v ~b v ~c, c], sat).
prove_tests(xyz, validity, [x v ~y v z, x v ~y v ~z, ~x v ~y v z], sat).
prove_tests(abc, validity, [a v b v c, a v b v ~c, a v ~b v ~c, a v ~b v c], sat).
prove_tests(a, validity, [a], sat).
prove_tests(read_it, performance, [i v t v t v o v o v k v m v e v s v o v l v o v n v g v t v o v i v n v e v n v t v w v h v a v t v t v o v w v r v i v t v e v h v e v r v e, ~h v ~e v ~r v ~e v ~i v ~s v ~g v ~o v ~n v ~n v ~a v ~b v ~e v ~s v ~e v ~c v ~o v ~n v ~d v ~c v ~l v ~a v ~u v ~s v ~e], sat).
prove_tests(why_not, performance, [b v ~b, a v t v ~i, i v ~i v a v t], sat).
prove_tests(you_re_gonna_fail, performance, [a v b v ~o v p v ~e, n v ~u v o v ~p v e v e v ~ w , q v ~p v b v ~n v y v ~t v i v ~i, o v m v p v ~w v q v p v m v e v ~p], sat).
prove_tests(n_th_set, validity, [b v ~c v a v c v d, ~d v ~a v c, d v ~c v b, d v ~e, e v d v ~a], sat).
prove_tests(theres_surprise, performance, [b v ~n v o v p v ~y v r v w v p v ~i v o v ~r v q, m v ~b v s v e v q v ~c v p v ~t v u v r v ~d v l, a v m v ~p v ~i v ~z v ~y v i, [], a v ~a ], unsat).
prove_tests(try_to_handle_it, performance, [a v b v ~t v y v ~i, i v o v ~b v ~y v a v m , ~m v y v i v ~t v b v ~a v g, ~a v ~b v t v ~y v i v ~m, a v ~b v i v ~i v ~o v o, k v p v ~u v ~i v o v ~e v q], sat).
