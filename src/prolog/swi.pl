/*   Author: Frank Young <Frank.Young@sensors.wpafb.af.mil> */
/*  Created: 21 Jul 98 */
/* Updated: Wed Jul 21 17:02:00 1999 */
/* Filename: swi.pl */
/* Abstract: System predicates for SWI-Prolog. */ 

% Compiling with SWI-Prolog:
%
%	?- qcompile('lptp.pl').
% 	?- halt.
%
% A file `lptp.qlf' is created.


%%d io__lptp_home(gr::out)

io__lptp_home('/home/staerk/lptp').

%%d io__path_sep(gr::out)

io__path_sep(/).

%%d io__get_stream(gr::in,gr::in,gr::out)

io__get_stream(File,Mode,Stream) :-
	open(File,Mode,Stream).

%%d io__set_output(gr::in)

io__set_output(Stream) :- set_output(Stream).

%%d io__set_input(gr::in)

io__set_input(Stream) :- set_input(Stream).

%%d db__user_stream(gr::out)

:- dynamic db__user_stream/1.

db__user_stream(user).

%%d io__original_user(gr::out)

io__original_user(user).

%%d read_with_variables(any,any)

read_with_variables(Term,VarL) :-
	read_term(Term,[variable_names(VarL)]).

% Example:
% 
% | ?- read_term([variable_names(L)],T).
% |: f(X,_Y,_,X).
% 
% L = ['X'=_6711,'_Y'=_6728],
% T = f(_6711,_6728,_6745,_6711) ;

%%d io__exec_file(gr::in)

io__exec_file(File) :- consult(File).

%%d initialization(any)

initialization(Goal) :- call(Goal).

% swi.pl ends here
