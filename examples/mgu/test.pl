%~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
% Testing and Debugging
%~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

member(X,[X|_]).
member(X,[_|L]) :-
	member(X,L).

%messages(yes).
messages(no).

test_max(19).

test(1) :- 
	test_unifiable($(x),$(x),S),
	S = [].

test(2) :-
	test_unifiable([c],[c],S),
	S = [].

test(3) :-
	test_unifiable($(x),$(y),S),
	S = [bind(x,$(y)),bind(y,$(y))].

test(4) :-
	test_unifiable([f,$(x),$(x)],[f,$(y),[g,[c]]],S),
	S = [bind(x,[g,[c]]),bind(y,[g,[c]])].

test(5) :- test_not_unifiable([f,$(x)],[g,[c]]).

test(6) :- test_not_unifiable($(x),[f,$(y),$(y),[c],[c],$(x)]).

test(7) :-
	P = 
	   [cl([f,$(x1),$(x1)],[cl($(x0),[])]),
	    cl([f,$(x2),$(x2)],[cl($(x1),[])]),
	    cl([f,$(x3),$(x3)],[cl($(x2),[])]),
	    cl([f,$(x4),$(x4)],[cl($(x3),[])]),
	    cl([f,$(x5),$(x5)],[cl($(x4),[])]),
	    cl([f,$(x6),$(x6)],[cl($(x5),[])]),
	    cl([f,$(x7),$(x7)],[cl($(x6),[])]),
	    cl([f,$(x8),$(x8)],[cl($(x7),[])]),
	    cl([f,$(x9),$(x9)],[cl($(x8),[])]),
	    cl([f,$(x10),$(x10)],[cl($(x9),[])]),
	    cl([f,$(x11),$(x11)],[cl($(x10),[])]),
	    cl([f,$(x12),$(x12)],[cl($(x11),[])]),
	    cl([f,$(x13),$(x13)],[cl($(x12),[])]),
	    cl([f,$(x14),$(x14)],[cl($(x13),[])]),
	    cl([f,$(x15),$(x15)],[cl($(x14),[])]),
	    cl([f,$(x16),$(x16)],[cl($(x15),[])]),
	    cl([f,$(x17),$(x17)],[cl($(x16),[])]),
	    cl([f,$(x18),$(x18)],[cl($(x17),[])]),
	    cl([f,$(x19),$(x19)],[cl($(x18),[])]),
	    cl([f,$(x20),$(x20)],[cl($(x19),[])])],
	partition(P),
	cycle_free(P).


test(8) :-
	P = [cl([f,$(x1),$(x1)],[cl($(x0),[])]),
	     cl([f,$(x2),$(x2)],[cl($(x1),[])]),
	     cl([f,$(x3),$(x0)],[cl($(x2),[])])],
	partition(P),
	\+ cycle_free(P).

test(9) :-
	test_unifiable($(x),[f,$(y)],S),
	S = [bind(x,[f,$(y)])].


test(10) :-
	test_unifiable([f,[g,$(x)],$(y)],[f,$(z),$(z)],S),
	S = [bind(z,[g,$(x)]),bind(y,[g,$(x)])].

test(11) :-
	test_unifiable([f,$(x),$(y)],[f,$(y),$(x)],S),
	S = [bind(x,$(y)),bind(y,$(y))].

test(12) :-
	test_unifiable([f,[f,[f,[a],$(x1)],$(x2)],$(x3)],
		[f,$(x3),[f,$(x2),[f,$(x1),[a]]]],S),
	S = [bind(x3,[f,[f,[a],[a]],[f,[a],[a]]]),
		bind(x2,[f,[a],[a]]),bind(x1,[a])].

test(13) :-
	test_not_unifiable([f,$(z),[g,[g,[g,[g,$(x)]]]]],
	[f,[g,$(z)],[g,[g,[g,[g,$(y)]]]]]).

test(14) :-
	test_not_unifiable([f,$(x),[g,$(x),[g,$(x),[g,$(x),[g,$(x),$(x)]]]],
		$(x)],
		[f,[g,$(y),[g,$(y),[g,$(y),[g,$(y),$(y)]]]],$(y),$(y)]).

test(15) :-
	test_not_unifiable([f,[f,[f,[f,[a],$(x1)],$(x2)],$(x3)],$(x4)],
		[f,$(x4),[f,$(x3),[f,$(x2),[f,$(x1),[b]]]]]).

test(16) :-
	test_not_unifiable([f,$(x),[g,[g,[g,[g,$(x)]]]],$(x)],
		[f,[g,[g,[g,[g,$(y)]]]],$(y),$(y)]).

test(17) :-
	test_unifiable([f,[g,[g,[g,[g,$(x)]]]]],[f,[g,[g,[g,[g,$(y)]]]]],S),
	S = [bind(x,$(y)),bind(y,$(y))].

test(18) :-
	test_not_unifiable([f,[f,[f,[f,[f,[a],$(x1)],$(x2)],$(x3)],$(x4)],
		$(z)],
		[f,[f,$(x4),[f,$(x3),[f,$(x2),[f,$(x1),[a]]]]],[g,$(z)]]).

test(19) :-
	test_not_unifiable([f,$(x),$(y),$(x)],
		[f,[h,$(x),$(x)],[h,$(y),$(y)],$(y)]).




test :-
	\+ not_test.

not_test :-
	test_max(M),
	test_gen(M,1,N),
	\+ test_ok(N).

test_gen(_,M,M).
test_gen(K,M1,J) :-
	M1 < K,
	M2 is M1 + 1,
	test_gen(K,M2,J).

test_ok(N) :-
	write(test(N)),
	test(N),
	write(' O.K.'), nl.


test_unifiable(T1,T2,S) :-
	term(T1),
	term(T2),
	unify_terms_part(T1,T2,P),
	partition(P),
	message('Yes, it is a partition.'),
	solved(P),
	message('Yes, is in solved form.'),
	partition_sub(P,P,[],S),
	substitution(S),
	message('Yes, we have a substitution.'),
	partition_solution(P,S),
	message('Yes, it is a solution.'),
	unifier(T1,T2,S),
	message('Yes, it is a unifier.').

test_not_unifiable(T1,T2) :-
	term(T1),
	term(T2),
	\+ unifiable_terms(T1,T2).

message(X) :-
	(	messages(yes) ->
		nl, write(X)
	;	true
	).

