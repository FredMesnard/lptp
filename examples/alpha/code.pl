:- op(700,xfy,#=<).
:- op(700,xfy,#<).

/* Generic predicates are:

   val(X)
   U #=< V
   pos(X)
   and_pos(X)
   or_pos(X)
   static_value(X,V)
   moves(X,L)

Special constants are: 

   bot
   top

*/

U #< V :- U #=< V, not(U = V).

pos_list([]).
pos_list([X|L]) :- pos(X), pos_list(L).


/* Predicates for min-max. */

min_max(P,0,V) :- 
	static_value(P,V).

min_max(P,s(N),V) :- 
	and_pos(P),
	moves(P,L),
	min_list(L,N,V).

min_max(P,s(N),V) :- 
	or_pos(P),
	moves(P,L),
	max_list(L,N,V).

min_list([],_,top).

min_list([X|L],N,V) :- 
	min_max(X,N,V1),
	min_list(L,N,V2),
	min(V1,V2,V).

min(V1,V2,V) :- 
	(	V1 #=< V2 ->
		V = V1
	;	V = V2
	).

max_list([],_,bot).

max_list([X|L],N,V) :- 
	min_max(X,N,V1),
	max_list(L,N,V2),
	max(V1,V2,V).

max(V1,V2,V) :- 
	(	V1 #=< V2 ->
		V = V2
	;	V = V1
	).

/* Predicates for alpha-beta. */

alpha_beta(_,_,P,0,V) :- 
	static_value(P,V).

alpha_beta(A,B,P,s(N),V) :- 
	and_pos(P),
	moves(P,L),
	beta_list(A,B,L,N,V).

alpha_beta(A,B,P,s(N),V) :- 
	or_pos(P),
	moves(P,L),
	alpha_list(A,B,L,N,V).

beta_list(A,B,L,_,B) :- 
	(	B #=< A
    	;	L = []
	).
    

beta_list(A,B,[P|L],N,V) :- 
	A #< B,
	alpha_beta(A,B,P,N,V1),
	min(B,V1,V2),
	beta_list(A,V2,L,N,V).

alpha_list(A,B,L,_,A) :- 
	(	B #=< A
        ;	L = []
	).

alpha_list(A,B,[P|L],N,V) :- 
	A #< B,
	alpha_beta(A,B,P,N,V1),
	max(A,V1,V2),
	alpha_list(V2,B,L,N,V).
 
