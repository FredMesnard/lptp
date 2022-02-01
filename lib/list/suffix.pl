prefix([],L).
prefix([X|L1],[X|L2]) :- prefix(L1,L2).

suffix(L,L).
suffix(L1,[Y|L2]) :- suffix(L1,L2).

sublist1(L1,L2) :- prefix(L3,L2), suffix(L1,L3).

sublist2(L1,L2) :- suffix(L3,L2), prefix(L1,L3).
