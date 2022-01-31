a0(X,Z) :- (b(X,Y) -> c(Y,Z); d(X,Z)).

a1(X,Z) :- (b(X,Y) -> c(Y,Z)).

b(0,0).
b(0,1).

c(0,a).
c(0,b).
c(1,c).
c(1,d).

d(0,x).
d(1,e).
d(1,f).


t1 :-
	bagof(Z,a0(0,Z),L), L = [a,b].
t2 :-
	bagof(Z,a0(1,Z),L), L = [e,f].
	
t3 :-
	(a,b -> c,d ; e,f) = ';'(->(','(a,b),','(c,d)),','(e,f)).

t4 :-
	bagof(Z,a1(0,Z),L), L = [a,b].

test_if :-
	t1, t2, t3, t4, write('*** test_if o.k.'), nl.

:- initialization(test_if).
