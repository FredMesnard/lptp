d_list([],D).
d_list([X|L],D) :-
	call(D,X),
	d_list(L,D).

permutation_sort(L1,L2,R) :-
	permutation(L1,L2),
	r_ordered(L2,R).

r_ordered([],R).
r_ordered([X],R).
r_ordered([X,Y|L],R) :-
	(	X = Y
	;	call(R,X,Y)
	),
	r_ordered([Y|L],R).

insert_sort([],[],R).
insert_sort([X|L1],L3,R) :-
	insert_sort(L1,L2,R),
	insert(X,L2,L3,R).
	
insert(X,[],[X],R).
insert(X,[Y|L1],L3,R) :-
	(	call(R,X,Y) ->
		L3 = [X,Y|L1]
	;	L3 = [Y|L2],
		insert(X,L1,L2,R)
	).

quick_sort(L1,L2,R) :- quick_sort(L1,[],L2,R).

quick_sort([],L,L,R).
quick_sort([X|L1],L2,L6,R) :-
	split(X,L1,L3,L4,R),
	quick_sort(L3,L2,L5,R),
	quick_sort(L4,[X|L5],L6,R).

split(X,[],[],[],R).
split(X,[Y|L1],L2,L3,R) :-
	(	call(R,X,Y) -> 
		L2 = [Y|L4], 
		L3 = L5
	; 	L2 = L4, 
		L3 = [Y|L5]
	),
	split(X,L1,L4,L5,R).
		
% Prolog without call/n+1 needs:
%
% call(R,X) :- G =.. [R,X], call(G).
% call(R,X,Y) :- G =.. [R,X,Y], call(G).
