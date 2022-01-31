/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: 6/15/95, 12:04 AM */
/* Filename: main.pl */
/* Abstract: This is a temporary file for testing of the files grammar.pl,
dcg_grammar.pl, read.pl, write.pl, tokens.pl, chars?.pl. */

%% Open Prolog
%:- unknown(X,trace).

append([],L,L).
append([X|L1],L2,[X|L3]) :- append(L1,L2,L3).

member(X,[X|_]).
member(X,[_|L]) :- member(X,L).


:- ['chars3.pl'].
:- ['tokens.pl'].
:- ['grammar.pl'].
:- ['dcg_grammar.pl'].
:- ['read.pl'].
:- ['write.pl'].

pread(T) :-
	read_token_list(L), !,
	parse(L,T).

test_read(F) :-
	see(F),
	repeat,
	pread(T),
	writeq(T), nl,
	(	T = con(end_of_file) -> 
		seen
	; 	fail
	).
	
test_tokens(F) :-
	see(F),
	repeat,
	read_token_list(L),
	writeq(L), nl,
	(	member(name(end_of_file),L) -> 
		seen
	; 	fail
	).

