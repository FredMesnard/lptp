%   Author: Robert F. Staerk <robert.staerk@unifr.ch> 
%  Created: Fri Jun  5 11:17:07 1998 
% Filename: mgu.pl 
% Abstract: A union-find based unification algorithm. The algoritm
% is used in the LPTP system. See: `lptp/src/mgu.pl'.

%~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
% Specification
%~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

% term(T) means: T is a term.
% Example: The term f(X,Y,c) is encoded as [f,$(x),$(y),[c]].
% The variable X is encoded as $(x).

term($(X)) :-
	atomic(X).
term([X|TL]) :-
	atomic(X),
	termL(TL).

% termL(TL) means: TL is a list of terms.

termL([]).
termL([T|TL]) :-
	term(T),
	termL(TL).

% subterm(T1,T2) means: T1 is a subterm of T2.

subterm(T,T).
subterm(T,[_|TL]) :- 
	subtermL(T,TL).

subtermL(T1,TL) :-
	member(T2,TL),
	subterm(T1,T2).

% var_form(T) means: T has the form of a variable.

var_form($(_)).

% size(T,N) means: The size of the term T is N. 
% N is a successor number, e.g. 0, s(0), s(s(0)), s(s(s(0))), ...

size($(_),s(0)).
size([_|TL],s(N)) :- sizeL(TL,N).

% sizeL(TL,N) means: The size of the termlist TL is N.

sizeL([],0).
sizeL([T|TL],N3) :-
	size(T,N1),
	sizeL(TL,N2),
	plus(N1,N2,N3).

% substitution(S) means: S is a substitution. A substitution S is a list of
% bindings of the form bind(X,T), where X is the name of a variable and T is
% a term. For each X there is at most one binding bind(X,T) in S.

substitution([]).
substitution([bind(X,T)|S]) :-
	atomic(X),
	term(T),
	substitution(S),
	\+ domain(X,S).

% domain(X,S) means: X is in the domain of the substitution S.
% There exists a binding bind(X,T) in S.

domain(X,S) :- member(bind(X,_),S).

% apply(T1,S,T2) means: T2 is the result of applying the substitution S
% to the term T1.

apply($(X),S,T) :- assoc(X,S,T).
apply([X|T1L],S,[X|T2L]) :-
	applyL(T1L,S,T2L).

applyL([],_,[]).
applyL([T1|T1L],S,[T2|T2L]) :-
	apply(T1,S,T2),
	applyL(T1L,S,T2L).

% assoc(X,S,T) means: S applied to the variable $(X) yields T.

assoc(X,[],$(X)).
assoc(X,[bind(X,T)|_],T).
assoc(X,[bind(Y,_)|S],T) :-
	\+ X = Y,
	assoc(X,S,T).

% class(C) means: C is a class (a tree of terms). A class has the form
% cl(T,P). T is a term. It is the root of the class. P is the list of
% the children of T. P is called a partition. P is a list of classes.
% If the root of a class is a variable, then all its members must be
% variables.

class(cl(T,P)) :-
	term(T),
	partition(P),
	\+ partition_member(T,P),
	\+ not_var_class(T,P).

not_var_class($(_),P) :-
	partition_member(T,P),
	\+ var_form(T).

% partition(P) means: P is a partition (a list of disjoint classes).

partition([]).
partition([C|P]) :-
	class(C),
	partition(P),
	disjoint(C,P).

% disjoint(C,P) means: class C and partition P are disjoint.

disjoint(C,P) :-
	\+ not_disjoint(C,P).

not_disjoint(C,P) :-
	class_member(T,C),
	partition_member(T,P).

% class_solution(C,S) means: S is a solution of the class C, i.e.
% S unifies all terms of C.

class_solution(C,S) :-
	\+ not_class_solution(C,S).

not_class_solution(C,S) :-
	class_member(T1,C),
	class_member(T2,C),
	apply(T1,S,T3),
	apply(T2,S,T4),
	\+ T3 = T4.

% partition_solution(P,S) means: the substitution S is a solution of 
% the partition P.

partition_solution([],_).
partition_solution([C|P],S) :-
	class_solution(C,S),
	partition_solution(P,S).

% unifier(T1,T2,S) means: Substitution S is a unifier of T1 and T2.

unifier(T1,T2,S) :-
	apply(T1,S,T3),
	apply(T2,S,T3).

% unifierL(TL1,TL2,S) means: Substitution S is a unifier of the term lists
% TL1 and TL2.

unifierL([],[],_).
unifierL([T1|TL1],[T2|TL2],S) :-
	unifier(T1,T2,S),
	unifierL(TL1,TL2,S).

% solved(P) means: Partition P is in solved form.
% If C is a class of P with root [F|S1,...,Sm] and [G|T1,...,Tn] is
% an element of C, then F is equal to G, m is equal to n, and the
% term Si is equivalent to Ti with respect to P.

solved(P) :-
	\+ not_solved(P).

not_solved(P) :-
	member(cl([X1|T1L],P1),P),
	partition_member([X2|T2L],P1),
	(	\+ X1 = X2
	;	\+ equivalentL(T1L,T2L,P)
	).

% equivalent(T1,T2,P) means: T1 and T2 are equivalent with respect to
% the partition (equivalence relation) P. It means that T1 and T2 belong
% to the same class of P.

equivalent(T1,T2,P) :-
	find(P,T1,T),
	find(P,T2,T).

equivalentL([],[],_).
equivalentL([T1|T1L],[T2|T2L],P) :-
	equivalent(T1,T2,P),
	equivalentL(T1L,T2L,P).

% Successor relations for trees in equivalence relations.

parent(C,cl(_,P)) :- member(C,P).

parent_star(C,C).
parent_star(C1,C3) :-
	parent_star(C1,C2),
	parent(C2,C3).

parent_partition(C1,P) :-
	member(C2,P),
	parent_star(C1,C2).

parent_terms(T1,T2,P) :-
	parent_partition(cl(T2,Q),P),
	member(cl(T1,_),Q).

%~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
% Implementation
%~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

% unifiable_terms(T1,T2) means: T1 and T2 can be unified using the 
% union-find algorithm.

unifiable_terms(T1,T2) :-
	unify_terms_part(T1,T2,_).

% unify_terms_part(T1,T2,P) means: T1 and T2 can be unified using the
% union-find algorithm. The result is the solved, cycle-free partition P.

unify_terms_part(T1,T2,P) :- 
	union_find(T1,T2,[],P),
	cycle_free(P).

% unify_terms_sub(T1,T2,S) means: Try to unify the two terms T1 and T2
% using the union find algorithm. If they are unifiable, convert the
% solved, cycle-free partition into a unifying substitution.

unify_terms_sub(T1,T2,S) :-
	unify_terms_part(T1,T2,P),
	partition_sub(P,P,[],S).

% union_find(T1,T2,P1,P2) means: 

union_find(T1,T2,P1,P4) :-
	find_delete(P1,T1,P2,C1),
	(	class_member(T2,C1) -> 
		P4 = P1
	;	find_delete(P2,T2,P3,C2),
		C1 = cl(T3,Q1),
		C2 = cl(T4,Q2),
		(	var_form(T3) ->
			P4 = [cl(T4,[C1|Q2])|P3]
		;	var_form(T4) ->
			P4 = [cl(T3,[C2|Q1])|P3]
		;	T3 = [Tag|T1L], 
			T4 = [Tag|T2L],
			union_findL(T1L,T2L,
				[cl(T4,[C1|Q2])|P3],P4)
	    	)
	).

union_findL([],[],P,P).
union_findL([T1|T1L],[T2|T2L],P1,P3) :-
	union_find(T1,T2,P1,P2),
	union_findL(T1L,T2L,P2,P3).

% class_member(T,C) means: T belongs to the class C.

class_member(T,cl(T,_)).
class_member(T,cl(_,P)) :-
	partition_member(T,P).

% partition_member(T,P) means: T belongs to one of the classes of P.

partition_member(T,[C|_]) :-
	class_member(T,C).
partition_member(T,[_|P]) :-
	partition_member(T,P).

% find(P,T1,T2) means: T1 belongs to the class with root T2 in P.

find([],T,T).
find([C|P],T1,T2) :-
	(	class_member(T1,C) ->
		C = cl(T2,_)
	;	find(P,T1,T2)
	).

% find_delete(P1,T,P2,C) means: find the class C of P1 to which T belongs.
% Delete C in P1 to obtain P2.

find_delete([],T,[],cl(T,[])).
find_delete([C1|P1],T,P3,C2) :-
	(	class_member(T,C1) -> 
		C2 = C1,
		P3 = P1
	;	find_delete(P1,T,P2,C2),
		P3 = [C1|P2]
	).

% cycle_free(P) means: the partition P is cycle free.

cycle_free(P) :-
	roots(P,TL),
	cycle_freeL(TL,P,[],[],_).

% roots(P,TL) means: TL is the list of the roots of the classes of P.

roots([],[]).
roots([cl(T,_)|P],[T|TL]) :-
	roots(P,TL).

% cycle_freeL(TL,P,C,WF1,Wf2) means: Check whether the terms in
% TL are in the cycle-free part of P. C is the path to the terms in TL.
% WF1 is a list of nodes which are already in the cycle-free part of P.
% WF2 is the output list of nodes which are in the cycle-free part of P.
% WF2 extends WF1. WF2 is a so-called topological ordering of P.

cycle_freeL([],_,_,WF,WF).
cycle_freeL([T1|T1L],P,C,WF1,WF3) :-
	find(P,T1,T2),
	(	member_check(T2,C) ->
		fail
	;	member_check(T2,WF1) ->
		cycle_freeL(T1L,P,C,WF1,WF3)
	;	var_form(T2) ->
		cycle_freeL(T1L,P,C,[T2|WF1],WF3)
	;	T2 = [_|T2L],
		cycle_freeL(T2L,P,[T2|C],WF1,WF2),
		cycle_freeL(T1L,P,C,[T2|WF2],WF3)
	).

% member_check(X,L) means: Check whether X belongs to L.

member_check(X,[Y|L]) :-
	(	X = Y ->
		true
	;	member_check(X,L)
	).

% partition_sub(P1,P2,S1,S2) means: Extend substitution S1 to S2. Go through
% the classes of P1. Look for variables. Take variables. Expand them to terms
% according to the partition P2. Add the bindings to S1. The result is S2.

partition_sub([],_,S,S).
partition_sub([C|P1],P2,S1,S3) :-
	class_sub(C,P2,S1,S2),
	partition_sub(P1,P2,S2,S3).

class_sub(cl($(X),P1),P2,S1,S2) :-
	partition_term($(X),P2,T),
	partition_sub(P1,P2,[bind(X,T)|S1],S2).
class_sub(cl([_|_],P1),P2,S1,S2) :-
	partition_sub(P1,P2,S1,S2).

% partition_term(T1,P,T2) means: Expand term T1 into term T2 according to P.

partition_term(T1,P,T3) :-
	find(P,T1,T2),
	(	var_form(T2) ->
		T3 = T2
	;	T2 = [Tag|T1L],
		partition_termL(T1L,P,T2L),
		T3 = [Tag|T2L]
	).

partition_termL([],_,[]).
partition_termL([T1|T1L],P,[T2|T2L]) :-
	partition_term(T1,P,T2),
	partition_termL(T1L,P,T2L).

