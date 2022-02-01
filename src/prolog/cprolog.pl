/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: Fri Dec  2 15:50:25 1994 */
/* Updated: Wed Jul 21 13:15:10 1999 */
/* Filename: cprolog.pl */
/* Abstract: System predicates for C-Prolog version 1.5, Unix. */

%%d io__lptp_home(gr::out)

io__lptp_home('/home/staerk/lptp').

%%d io__path_sep(gr::out)

io__path_sep(/).

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

%%d abolish(any)

abolish(Name/N) :- abolish(Name,N).

%%d once(gr::in)

once(Goal) :- call(Goal), !.

%%d io__get_stream(gr::in,gr::in,gr::out)

io__get_stream(File,_,File).

%%d io__set_output(gr::in)

io__set_output(Stream) :- tell(Stream).

%%d io__set_input(gr::in)

io__set_input(Stream) :- see(Stream).

%%d db__user_stream(gr::out)

db__user_stream(user).

%%d io__original_user(gr::out)

io__original_user(user).

%%d dynamic(any)

:- op(1150,fx,dynamic).

dynamic(_).

%%d read_with_variables(any,any)

read_with_variables(Term,[]) :- read(Term).

%%d io__exec_file(gr::in)

io__exec_file(File) :- consult(File).

%%d initialization(any)

initialization(Goal) :- call(Goal).

% cprolog.el ends here

