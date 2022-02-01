ackermann(0,N,s(N)).
ackermann(s(M),0,N) :- 
	ackermann(M,s(0),N).
ackermann(s(M),s(N),K2) :-
	ackermann(s(M),N,K1),
	ackermann(M,K1,K2).
