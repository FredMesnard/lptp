permutation_sort(L1,L2) :-
	permutation(L1,L2),
	ordered(L2).

ordered([]).
ordered([X]).
ordered([X,Y|L]) :- X @=< Y, ordered([Y|L]).

insert_sort([],[]).
insert_sort([X|L1],L3) :-
	insert_sort(L1,L2),
	insert(X,L2,L3).
	
insert(X,[],[X]).
insert(X,[Y|L],[X,Y|L]) :- X @=< Y.
insert(X,[Y|L1],[Y|L2]) :- not(X @=< Y), insert(X,L1,L2).

quick_sort(L1,L2) :- quick_sort(L1,[],L2).

quick_sort([],L,L).
quick_sort([X|L1],L2,L6) :-
	split(X,L1,L3,L4),
	quick_sort(L3,L2,L5),
	quick_sort(L4,[X|L5],L6).

% split(X,[],[],[]).
% split(X,[Y|L1],[Y|L2],L3) :- X @=< Y, split(X,L1,L2,L3).
% split(X,[Y|L1],L2,[Y|L3]) :- not(X @=< Y), split(X,L1,L2,L3).

split(X,[],[],[]).
split(X,[Y|L1],L2,L3) :-
	(	X @=< Y -> 
		L2 = [Y|L4], 
		L3 = L5
	; 	L2 = L4, 
		L3 = [Y|L5]
	),
	split(X,L1,L4,L5).
		
