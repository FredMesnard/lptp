list([]).
list([X|L]) :- list(L).

member(X,[X|L]).
member(X,[Y|L]) :- member(X,L).

append([],L,L).
append([X|L1],L2,[X|L3]) :- append(L1,L2,L3).

length([],0).
length([X|L],s(N)) :- length(L,N).

delete(X,[X|L],L).
delete(X,[Y|L1],[Y|L2]) :- delete(X,L1,L2).

