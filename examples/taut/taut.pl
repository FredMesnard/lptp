list([]).
list([X|L]) :- list(L).

member(X,[X|L]).
member(X,[Y|L]) :- member(X,L).

formula(p(X)).
formula(neg(A)) :- formula(A).
formula(and(A,B)) :- formula(A), formula(B).
formula(or(A,B)) :- formula(A), formula(B).

literal(p(X)).
literal(neg(p(X))).

literal_list([]).
literal_list([A|I]) :-
	literal(A),
	literal_list(I).

interpretation(I) :- literal_list(I), not incon(I).

incon(I) :- member(p(X),I), member(neg(p(X)),I).

valid(A) :- not satisfiable(neg(A)).

satisfiable(A) :- true(A,[],I).

true(p(X),I,[p(X)|I]) :- not member(neg(p(X)),I).
true(neg(A),I,J) :- false(A,I,J).
true(and(A,B),I,K) :- true(A,I,J), true(B,J,K).
true(or(A,B),I,J) :- true(A,I,J).
true(or(A,B),I,J) :- true(B,I,J).

false(p(X),I,[neg(p(X))|I]) :- not member(p(X),I).
false(neg(A),I,J) :- true(A,I,J).
false(and(A,B),I,J) :- false(A,I,J).
false(and(A,B),I,J) :- false(B,I,J).
false(or(A,B),I,K) :- false(A,I,J), false(B,J,K).

eval(p(X),I,1) :- member(p(X),I).
eval(p(X),I,0) :- member(neg(p(X)),I).
eval(neg(A),I,1) :- eval(A,I,0).
eval(neg(A),I,0) :- eval(A,I,1).
eval(and(A,B),I,1) :- eval(A,I,1), eval(B,I,1).
eval(and(A,B),I,0) :- eval(A,I,0).
eval(and(A,B),I,0) :- eval(B,I,0).
eval(or(A,B),I,1) :- eval(A,I,1).
eval(or(A,B),I,1) :- eval(B,I,1).
eval(or(A,B),I,0) :- eval(A,I,0), eval(B,I,0).

defined(p(X),I) :- member(p(X),I).
defined(p(X),I) :- member(neg(p(X)),I).
defined(neg(A),I) :- defined(A,I).
defined(and(A,B),I) :- defined(A,I), defined(B,I).
defined(or(A,B),I) :- defined(A,I), defined(B,I).
