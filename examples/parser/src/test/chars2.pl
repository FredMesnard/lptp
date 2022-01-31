/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: 7/13/95, 4:54 PM */
/* Filename: chars2.pl */
/* Abstract: The class of a character. Version with if-then-else. The
predicate char_class/2 is used in tokens.pl . */

char_class(N,C) :-
	(	97 =< N, N =< 122 -> C = alpha_num(small_letter)
	;	65 =< N, N =< 90 -> C = alpha_num(capital_letter)
	;	48 =< N, N =< 57 -> C = alpha_num(decimal_digit)
	;	N = 95 -> C = alpha_num(capital_letter) 	% _
	;	N = 40  -> C = solo(open(layout)) 		% (
	;	N = 41  -> C = solo(close) 			% )
	;	N = 44  -> C = solo(comma) 			% ,
	;	1 =< N , N =< 32 ->
		(	(N = 31 ; N = 10) -> C = layout(new_line)
		;	N = 26 -> C = end_of_file		% Mac ???
		;	C = layout(space)
		)
	;	N = 91  -> C = solo(open_list) 			% [
	;	N = 93  -> C = solo(close_list) 		% ]
	;	N = 124 -> C = solo(head_tail_sep) 		% |
	;	N = 46  -> C = graphic(end) 			% .
	;	N = 33  -> C = solo(name(!)) 			% !
	;	N = 39  -> C = single_quote 			% '
	;	N = 37  -> C = end_line_comment 		% %
	;	N = 38  -> C = graphic(plain) 			% &
	;	N = 42  -> C = graphic(comment_2) 		% *
	;	N = 43  -> C = graphic(plain) 			% +
	;	N = 45  -> C = graphic(plain) 			% -
	;	N = 47  -> C = graphic(comment_1) 		% /
	;	N = 58  -> C = graphic(plain) 			% :
	;	N = 59  -> C = solo(name(;)) 			% ;
	;	N = 60  -> C = graphic(plain) 			% <
	;	N = 61  -> C = graphic(plain) 			% =
	;	N = 62  -> C = graphic(plain) 			% >
	;	N = 63  -> C = graphic(plain) 			% ?
	;	N = 35  -> C = graphic(plain) 			% #
	;	N = 36  -> C = graphic(plain) 			% $
	;	N = 64  -> C = graphic(plain) 			% @
	;	N = 92  -> C = graphic(backslash) 		% \
	;	N = 94  -> C = graphic(plain) 			% ^
	;	N = 123 -> C = solo(open_curly) 		% {
	;	N = 125 -> C = solo(close_curly) 		% }
	;	N = 126 -> C = graphic(plain) 			% ~
	;	N = 34  -> C = double_quote 			% "
	;	N = 96  -> C = back_quote 			% `
	;	N = -1  -> C = end_of_file
	;	C = illegal).

% End of chars2.pl

