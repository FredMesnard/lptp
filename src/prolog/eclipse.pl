/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: Fri Dec  2 15:50:05 1994 */
/* Updated: Wed Jul 21 17:01:42 1999 */
/* Filename: eclipse.pl */
/* Abstract: System predicates for ECLiPSe, Unix. */

% Compiling in ECLiPSe:
%
% ?- nodbgcomp.

:- set_flag(print_depth,100).

%%d io__lptp_home(gr::out)

io__lptp_home('/home/staerk/lptp').

%%d io__path_sep(gr::out)

io__path_sep(/).

%%d io__get_stream(gr::in,gr::in,gr::out)

io__get_stream(File,Mode,Stream) :-
	open(File,Mode,Stream).

%%d io__set_output(gr::in)

io__set_output(Stream) :-
	set_stream(output,Stream).

%%d io__set_input(gr::in)

io__set_input(Stream) :-
	set_stream(input,Stream).

%%d db__user_stream(gr::out)

:- dynamic db__user_stream/1.

db__user_stream(1).

%%d io__original_user(gr::out)

io__original_user(1).

%%d read_with_variables(any,any)

read_with_variables(Term,VarL) :-
	read_term(Term,[variable_names(VarL)]).

% Example:
% 
% | ?- read_term(T,[variable_names(L)]).
% |: f(X,_Y,_,X).
% 
% L = ['X'=_6711,'_Y'=_6728],
% T = f(_6711,_6728,_6745,_6711)

%%d io__exec_file(gr::in)

io__exec_file(File) :- consult(File).

%%d initialization(any)

initialization(Goal) :- call(Goal).

% eclipse.pl ends here

