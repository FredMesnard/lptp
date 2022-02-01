/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: Fri Dec  2 15:49:51 1994 */
% Updated: Wed Jul 21 17:10:49 1999
/* Filename: sicstus.pl */
/* Abstract: System predicates for SICStus 3, SunOS. */

% Compiling with SICStus Prolog:
%
%	?- prolog_flag(compiling,_,fastcode). 
% 	?- consult('op.pl').
% 	?- fcompile('lptp.pl').
% 	?- halt.

%%d io__lptp_home(gr::out)

io__lptp_home('/home/staerk/lptp12').

%%d io__path_sep(gr::out)

io__path_sep(/).

%%d once(gr::in)

once(Goal) :- call(Goal), !.

%%d concat_atom(grL::in,gr::out)

concat_atom(AtomL,Atom) :-
	concat_atomL(AtomL,CharL),
	name(Atom,CharL).

%%d concat_atomL(grL::in,grL::out)

concat_atomL([],[]).
concat_atomL([Atom|AtomL],Char3L) :-
	concat_atomL(AtomL,Char1L),
	name(Atom,Char2L),
	lst__concat(Char2L,Char1L,Char3L).

%%d atomic_length(gr::in,int::out)

atomic_length(Atom,N) :-
	name(Atom,CharL),
	length(CharL,N).

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

%%d io__exec_file(gr::in)

io__exec_file(File) :- consult(File).

% sicstus.pl ends here

