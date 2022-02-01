n_reverse([],[]).
n_reverse([X|L1],L3) :- n_reverse(L1,L2), append(L2,[X],L3).

reverse(L1,L2) :- a_reverse(L1,[],L2).

a_reverse([],L,L).
a_reverse([X|L1],L2,L3) :- a_reverse(L1,[X|L2],L3).
