/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: 7/20/95, 8:15 PM */
/* Filename: chars3.pl */
/* Abstract: The class of a character. Version with cut. The predicate
char_class/2 is used in tokens.pl . */

char_class(N,C) :- 97 =< N, N =< 122, C = alpha_num(small_letter), !.
char_class(N,C) :- 65 =< N, N =< 90, C = alpha_num(capital_letter), !.
char_class(N,C) :- 48 =< N, N =< 57, C = alpha_num(decimal_digit), !.
char_class(95,alpha_num(capital_letter)) :- !.	% _
char_class(40,solo(open(layout))) :- !.		% (
char_class(41,solo(close)) :- !. 		% )
char_class(44,solo(comma)) :- !. 		% ,
char_class(10,layout(new_line)) :- !.
char_class(31,layout(new_line)) :- !.		% Macintosh, Open Prolog
char_class(26,end_of_file) :- !.		% Macintosh, Open Prolog
char_class(N,C) :- 1 =< N , N =< 32, C = layout(space), !.
char_class(91,solo(open_list)) :- !. 		% [
char_class(93,solo(close_list)) :- !.	 	% ]
char_class(124,solo(head_tail_sep)) :- !. 	% |
char_class(46,graphic(end)) :- !.	 	% .
char_class(33,solo(name(!))) :- !.	 	% !
char_class(39,single_quote ) :- !.		% '
char_class(37,end_line_comment) :- !.	 	% %
char_class(38,graphic(plain)) :- !. 		% &
char_class(42,graphic(comment_2)) :- !. 	% *
char_class(43,graphic(plain)) :- !. 		% +
char_class(45,graphic(plain)) :- !. 		% -
char_class(47,graphic(comment_1)) :- !. 	% /
char_class(58,graphic(plain)) :- !.		% :
char_class(59,solo(name(;))) :- !.	 	% ;
char_class(60,graphic(plain)) :- !. 		% <
char_class(61,graphic(plain)) :- !. 		% =
char_class(62,graphic(plain)) :- !. 		% >
char_class(63,graphic(plain)) :- !. 		% ?
char_class(35,graphic(plain)) :- !. 		% #
char_class(36,graphic(plain)) :- !. 		% $
char_class(64,graphic(plain)) :- !. 		% @
char_class(92,graphic(backslash)) :- !. 	% \
char_class(94,graphic(plain)) :- !. 		% ^
char_class(123,solo(open_curly)) :- !.	 	% {
char_class(125,solo(close_curly)) :- !. 	% }
char_class(126,graphic(plain)) :- !. 		% ~
char_class(34,double_quote) :- !.	 	% "
char_class(96,back_quote) :- !. 		% `
char_class(-1,end_of_file) :- !.
char_class(_,illegal).

% End of chars3.pl
