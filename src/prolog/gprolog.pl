/*   Author: Robert Staerk <staerk@math.stanford.edu> */
/*  Created: Fri Dec  2 15:49:51 1994 */
/* Updated: Wed Sep  1 13:37:28 1999 */
/* Filename: gprolog.pl */
/* Abstract: System predicates for GNU Prolog 1.0.0
   See: http://www.gnu.org/software/prolog/prolog.html  
   Use a large heap, eg. setenv GLOBALSZ 16384
*/

% Compiling with GNU Prolog
%
% unix> gplc --global-size 16384 -o lptp lptp.pl
%
% An executable file `lptp' is created.

%%d io__lptp_home(gr::out)

io__lptp_home('/home/staerk/lptp12').

%%d io__path_sep(gr::out)

io__path_sep(/).

% dynamic/1 is not an operator in gprolog

:- op(1150,fx,dynamic).

%%d assert(goal)

assert(Fact) :- assertz(Fact).

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
	(	atom(Atom) ->
		atom_length(Atom,N)
	;	number_chars(Atom,CharL),
		length(CharL,N)
	).

%%d io__get_stream(gr::in,gr::in,gr::out)

io__get_stream(File,Mode,Stream) :-
	open(File,Mode,Stream).

%%d io__set_output(gr::in)

io__set_output(Stream) :- set_output(Stream).

%%d io__set_input(gr::in)

io__set_input(Stream) :- set_input(Stream).

%%d db__user_stream(gr::out)

:- dynamic db__user_stream/1.

db__user_stream(user_output).

%%d io__original_user(gr::out)

io__original_user(user_output).

%%d read_with_variables(any,any)

read_with_variables(Term,VarL) :-
	read_term(Term,[variable_names(VarL)]).

% Example:
%
% | ?- read_term(T,[variable_names(L)]).
% f(X,_Y,_,X).
%
% L = ['X'=A,'_Y'=B]
% T = f(A,B,_,A)

% GNU Prolog does not support arbitary directives of the form `:- Goal'
% (in accordance with the ISO Prolog Standard). For example, it is not
% possible to include a file using `:- consult(file).'  Therefore we need
% a predicate that reads files consisting of directives and executes
% the directives.

%%d io__exec_file(gr::in)

io__exec_file(File) :-
	open(File,read,Stream),
	read(Stream,Term),
	io__loop_file(Stream,Term), !.

%%d io__loop_file(gr::in,gr::in)

io__loop_file(Stream,Term) :-
	(	Term = end_of_file ->
		close(Stream)
	;	io__exec_directive(Stream,Term), !,
		read(Stream,NextTerm), !,
		io__loop_file(Stream,NextTerm)
	).

%dd io__exec_directive(gr::in,gr::in)

io__exec_directive(Stream,Term) :-
	(	Term = :-(Goal), call(Goal) ->
		true
	;	stream_property(Stream,file_name(File)),
		ctl__warning([problem,in,File,with,Term])
	).

% gprolog.pl ends here

