/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: Wed Nov 23 23:45:29 1994 */
/* Updated: Wed Jul 21 13:17:38 1999 */
/* Filename: open.pl */
/* Abstract: System predicates for Open Prolog 1.0.3d20, Macintosh. */

% If a predicate has no definition the debugger is called.

:- unknown(X,trace).

%%d io__lptp_home(gr::out)

io__lptp_home('Macintosh HD:staerk:lptp').

%%d io__path_sep(gr::out)

io__path_sep(:).

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

%%d abolish(any)

abolish(Name/N) :- abolish(Name,N).

%%% Input/Output

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

%%d read_with_variables(any,any)

read_with_variables(Term,[]) :- read(Term).

%%d io__exec_file(gr::in)

io__exec_file(File) :- consult(File).

%%d initialization(any)

initialization(Goal) :- call(Goal).

% open.pl ends here

