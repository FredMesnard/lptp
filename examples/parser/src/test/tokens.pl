/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: 7/13/95, 4:57 PM */
/* Filename: tokens.pl */
/* Abstract: This file contains a tokenizer for (a subset of) ISO standard
Prolog. Charcter code constants of the form 0'* are not implemented according
to the standard and float numbers are not implemented. Some predicates in this
file are from a public-domain tokeniser by Richard A. O'Keefe (tokens.pl). The
predicate char_class/2 is defined (in different versions) in the files
``chars0.pl'', ``chars1.pl'', ``chars2.pl'' and ``chars3.pl''. The main
predicate of this file is read_token_list/1 which reads a sequence of
characters from the current input stream and returns a list of tokens. The
last token is always an end token. This tokenizer is not very efficient. */

% Tokens:
% 
% token(name(X)) :- atom(X).	% ',' ==> name(',')
% token(variable(X)) :- atom(X).
% token(integer(X)) :- integer(X).
% token(float_number(X)) :- number(X).
% token(char_code_list(X)) :- char_code_list(X).
% token(open(nolayout)).
% token(open(layout)).
% token(close).			% )
% token(open_list).		% [
% token(close_list).		% ]
% token(open_curly).		% {
% token(close_curly).		% }
% token(head_tail_sep).		% |
% token(comma).			% , ==> comma
% token(end).			% .

% Character classes:
%
% class(layout(space)).
% class(layout(new_line)).
% class(alpha_num(small_letter)).	% a-z
% class(alpha_num(capital_letter)).	% A-Z _
% class(alpha_num(decimal_digit)).	% 0-9
% class(solo(name(!))).			% !
% class(solo(open(layout))).		% (
% class(solo(close)).			% )
% class(solo(comma)).			% ,
% class(solo(name(;))).			% ;
% class(solo(open_list)).		% [
% class(solo(close_list)).		% ]
% class(solo(head_tail_sep)).		% |
% class(solo(open_curly)).		% {
% class(solo(close_curly)).		% }
% class(graphic(plain)).		% # $ & + - : < = > ? @ ^ ~
% class(graphic(comment_1)).		% /
% class(graphic(comment_2)).		% *
% class(graphic(backslash)).		% \
% class(graphic(end)).			% .
% class(end_line_comment).		% %
% class(single_quote).			% '				
% class(double_quote).			% "
% class(back_quote).			% `
% class(end_of_file).
% class(illegal).

% Variables:
%
% L: 	list of tokens
% M,N: 	ascii codes (-1,...,255)
% C: 	class of a character
% T:	token

next_char(C,N) :-
	get0(N),
	char_class(N,C), !.

read_token_list(L) :-
	next_char(C,N),
	read_token_list(C,N,L), !.
read_token_list(error(read_token_list)).

read_token_list(layout(_),_,L) :-
	next_char(C,N),
	read_token_list(C,N,L).
read_token_list(alpha_num(small_letter),N,L) :-
	read_identifier(N,L).
read_token_list(alpha_num(capital_letter),N,L) :-
	read_variable(N,L).
read_token_list(alpha_num(decimal_digit),N,L) :-
	read_number(N,L).
read_token_list(solo(T),_,[T|L]) :-
	next_char(C,N),
	(	T = name(_) ->
		read_after_name(C,N,L)
	;	read_token_list(C,N,L)
	).
read_token_list(graphic(X),N,L) :-
	(	X = comment_1 ->
		read_bracketed_comment(N,L)
	;	X = end ->
		read_full_stop(N,L)
	;	read_graphic(N,L)
	).
read_token_list(end_line_comment,_,L) :-
	read_end_line_comment,
	next_char(C,N),
	read_token_list(C,N,L).
read_token_list(single_quote,_,L) :-
	read_string(N_L,single_quote,C,N),
	read_after_name(N_L,C,N,L).
read_token_list(double_quote,_,[char_code_list(N_L)|L]) :-
	read_string(N_L,double_quote,C,N),
	read_token_list(C,N,L).
read_token_list(back_quote,_,[char_code_list(N_L)|L]) :-
	read_string(N_L,back_quote,C,N),
	read_token_list(C,N,L).
read_token_list(end_of_file,_,L) :-
	L = [name(end_of_file),end].
read_token_list(illegal,N,_) :-
	write('*** Warning: cannot read ascii '),
	write(N),
	write('.'), nl,
	fail.

read_identifier(M,L) :-
	read_name(M_L,C,N),
	read_after_name([M|M_L],C,N,L).

read_variable(M,[variable(A)|L]) :-
	read_name(M_L,C,N),
	name(A,[M|M_L]),
	read_token_list(C,N,L).

read_graphic(M,L) :-
	next_char(C1,N1),
	read_graphic_rest(C1,N1,M_L,C2,N2),
	read_after_name([M|M_L],C2,N2,L).

read_name(N1_L,C1,N1) :-
	next_char(C2,N2),
	(	C2 = alpha_num(_) ->
		N1_L = [N2|N2_L],
		read_name(N2_L,C1,N1)
	;	N1_L = [], 
		C1 = C2, 
		N1 = N2
	).

read_after_name(M_L,C,N,[name(X)|L]) :-
	name(X,M_L),
	read_after_name(C,N,L).

read_after_name(C1,N1,L1) :-
	(	C1 = solo(open(layout)) ->
		next_char(C2,N2),
		L1 = [open(nolayout)|L2],
		read_token_list(C2,N2,L2)
	;	read_token_list(C1,N1,L1)
	).

read_graphic_rest(C1,N1,N1_L,C2,N2) :-
	(	C1 = graphic(_) ->
		next_char(C3,N3),
		N1_L = [N1|N2_L],
		read_graphic_rest(C3,N3,N2_L,C2,N2)
	;	N1_L = [], 
		C2 = C1, 
		N2 = N1
	).

read_end_line_comment :-
	repeat,
	next_char(C,_),
	(	C = layout(new_line) -> 
		true
	; 	fail
	).

read_bracketed_comment(N,L) :-
	next_char(C1,N1),
	(	C1 = graphic(comment_2) ->
		read_comment_text,
		next_char(C2,N2),
		read_token_list(C2,N2,L)
	;	read_graphic_rest(C1,N1,N_L,C2,N2),
		read_after_name([N|N_L],C2,N2,L)
	).

read_comment_text :-
	repeat,
	next_char(C,_),
	(	C = graphic(comment_2) -> 
		read_comment_close
	; 	fail
	).

read_comment_close :-
	next_char(C,_),
	(	C = graphic(comment_1) ->
		true
	; 	C = graphic(comment_2) ->
		read_comment_close
	;	read_comment_text
	).

read_full_stop(N1,L) :-
	next_char(C2,N2),
	(	C2 = layout(_) -> 
		L = [end]
	;	C2 = end_line_comment ->
		read_end_line_comment, 
		L = [end]
	;	C2 = graphic(comment_1) ->
		next_char(C3,N3),
		(	C3 = graphic(comment_2) ->
			read_comment_text, 
			L = [end]
		;	read_graphic_rest(C3,N3,N_L,C4,N4),
			read_after_name([N1,N2|N_L],C4,N4,L)
		)
	;	read_graphic_rest(C2,N2,N_L,C3,N3),
		read_after_name([N1|N_L],C3,N3,L)
	).

read_number(M,[integer(I2)|L]) :-
	(	M = 48 /* 0 */ ->
		get0(K),
		(	K = 98  /* b */ -> read_integer(2,0,I2,C,N)
		; 	K = 111 /* o */ -> read_integer(8,0,I2,C,N)
		; 	K = 120 /* x */ -> read_integer(16,0,I2,C,N)
		;	digit(10,K,I1) -> read_integer(10,I1,I2,C,N)
		;   K = 39  /* quote */ -> get0(I2), next_char(C,N)
		; 	char_class(K,C), 
			I2 = 0, 
			N = K
		)
	;	I1 is M - 48,
		read_integer(10,I1,I2,C,N)
	),
	read_token_list(C,N,L).

read_integer(B,I1,I3,C,N) :-
	get0(M),
	(	digit(B,M,K) ->
		I2 is I1 * B + K,
		read_integer(B,I2,I3,C,N)
	;	char_class(M,C),
		I3 = I1, 
		N = M
	).

digit(10,N,K) :- 48 =< N, N =< 57,  K is N - 48.	% 0-9
digit(2,48,0).
digit(2,49,1).
digit( 8,N,K) :- 48 =< N, N =< 55,  K is N - 48.	% 0-7
digit(16,N,K) :- 48 =< N, N =< 57,  K is N - 48.	% 0-9
digit(16,N,K) :- 65 =< N, N =< 70,  K is N - 55.	% A-F
digit(16,N,K) :- 97 =< N, N =< 102, K is N - 87.	% a-f

read_string(N1_L,Q,C3,N3) :-
	next_char(C1,N1),
	(	C1 = Q ->
		next_char(C2,N2),
		(	C2 = Q ->			% QQ yields Q
			N1_L = [N2|N2_L],
			read_string(N2_L,Q,C3,N3)
		;	N1_L = [],			% string is termin.
			C3 = C2,
			N3 = N2
		)
	;	C1 = graphic(backslash) ->
		next_char(C2,N2),
		(	C2 = layout(new_line) ->	% cont. esc. seq.
			read_string(N1_L,Q,C3,N3)
		;	read_escape_sequence(N2,M),
			N1_L = [M|N2_L],
			read_string(N2_L,Q,C3,N3)
		)
	;	non_quote_class(C1) ->
		N1_L = [N1|N2_L],
		read_string(N2_L,Q,C3,N3)
	;	write('*** Error in quoted atom/string.'), 
		nl, 
		fail
	).

non_quote_class(graphic(_)).
non_quote_class(alpha_num(_)).
non_quote_class(solo(_)).
non_quote_class(layout(space)).
non_quote_class(single_quote).
non_quote_class(double_quote).
non_quote_class(back_quote).

read_escape_sequence(M,N) :-
	(	escape_char(M,N) ->	% control/meta escape sequence
		true
	;	digit(8,M,I) ->		% octal escape sequence
		read_integer(8,I,N,graphic(backslash),_)
	;	M = 120 /* x */ -> 	% hexadecimal escape sequence
		read_integer(16,0,N,graphic(backslash),_)
	;	write('*** Error: invalid escape sequence.'), 
		nl, fail
	).

escape_char(97,7). 		% "a" -> alert
escape_char(98,8). 		% "b" -> backspace
escape_char(102,12). 		% "f" -> form feed/new page
escape_char(110,10).		% "n" -> new line
escape_char(114,13).		% "r" -> carriage return
escape_char(116,9).		% "t" -> horizontal tab
escape_char(118,11).		% "v" -> vertical tab
escape_char(92,92).		% backslash -> backslash (\)
escape_char(39,39). 		% single_quote -> single_quote (')
escape_char(34,34). 		% double_quote -> double_quote (")
escape_char(96,96). 		% back_quote -> back_quote (`)

% End of tokens.pl

