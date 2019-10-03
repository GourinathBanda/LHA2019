:- module(input_ppl,[load_file/2,my_clause/2,invariant/2]).


:- dynamic my_clause/2.
:- dynamic invariant/2.

:- dynamic inputtype/1.
:- use_module(duplVar).
:- use_module(library(lists)).

load_file(F,Type) :-
    retractall(my_clause(_,_)),
    assert(inputtype(Type)),
	open(F,read,S),
	remember_all(S),
	close(S).

remember_all(S) :-
	read(S,C),
	(
	    C == end_of_file -> true
	;
	    remember_clause(C),
	    remember_all(S)
	).


remember_clause((invariant(A) :- B)) :-
%Invariant specs. are not added as my_clause/2
    (inputtype(pic) -> true, keepclauses(A)
    ;
    inputtype(pl) -> true),

!,
        headconstraints(A, ACs, Ant),
	writeAtomEq(Ant,Anodupl,Es,0,_K),
	
	tuple2list(B,BL),
        append(ACs,BL,BLhs),

	append(BLhs,Es,BLEs),

	assert(invariant(Anodupl,BLEs)).


remember_clause((A :- B)) :-
%only execute+specialize clauses are needed
    (inputtype(pic) -> true, keepclauses(A)
    ;
    inputtype(pl) -> true),

!,
        headconstraints(A, ACs, Ant),
	writeAtomEq(Ant,Anodupl,Es,0,_K),
	
	tuple2list(B,BL),
        append(ACs,BL,BLhs),

	append(BLhs,Es,BLEs),

%    write('Keep clause: '),write(Anodupl),nl.
	assert(my_clause(Anodupl,BLEs)).

remember_clause(A) :-
%	write('FACT '),write(A),nl,
   (inputtype(pic) -> true, keepclauses(A)
    ;
    inputtype(pl) -> true),
    !,
       headconstraints(A, ACs, Ant),
	writeAtomEq(Ant,Anodupl,Es,0,_K),
    	append(ACs,Es,BLEs),
%	write('FACT remcls '),write(Anodupl),write(' '),write(BLEs),nl,
	assert(my_clause(Anodupl,BLEs)).

%Drop all non-execute/specialize clauses
remember_clause(_).

keepclauses(A) :-
    A =.. [F|_],
    name(F,Fn),
    name(execute,En),
    conc(En,_,Fn).
keepclauses(A) :-
    A =.. [F|_],
    name(F,Fn),
    name(specialize,En),
    conc(En,_,Fn).

conc([],L,L).
conc([A|L1],L2,[A|L3]) :-
     conc(L1,L2,L3).

headconstraints(H,Cs,H1) :-
  H =.. [P|Xs],
  genConstraints(Xs,Ys,Cs),
  H1 =.. [P|Ys].

genConstraints([],[],[]).
genConstraints([X|Xs],[Y|Ys],[X=Y|HCs]) :-
     var(X),
     occurs(X,Xs),
     !,
     genConstraints(Xs,Ys,HCs).
genConstraints([X|Xs],[X|Ys],HCs) :-
     var(X),
     !,
     genConstraints(Xs,Ys,HCs).

genConstraints([T|Xs],[Y|Ys],[Y=T|HCs]):-
%    write('Term Should Be meltet: '),write(T),nl,
    genConstraints(Xs,Ys,HCs).

occurs(X,[Y|_]) :-
   X == Y,
   !.

occurs(X,[_|Ys]) :-
   occurs(X,Ys).



tuple2list((A,As),[A|LAs]) :-
	!,
	tuple2list(As,LAs).
tuple2list(A,[A]).

