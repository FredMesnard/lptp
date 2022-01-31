% Examples
%
% ?- bubble_sort([2,3,4,2],L,<).
% 
% L = [2,2,3,4]
%
% ?- bubble_sort([2,3,4,5],L,>).
% 
% L = [5,4,3,2]


bubble_sort([],[],R).
bubble_sort([X|L1],[Y|L3],R) :-
	bubble(X,L1,[Y|L2],R),
	bubble_sort(L2,L3,R).

bubble(X,[],[X],R).
bubble(X,[Y|L1],L3,R) :-
	bubble(Y,L1,[Z|L2],R),
	(	call(R,Z,X) ->
		L3 = [Z,X|L2]
	;	L3 = [X,Z|L2]
	).

% call(R,X,Y) :- G =.. [R,X,Y], call(G).
