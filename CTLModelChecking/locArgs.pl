:- module(locArgs,_).

:- use_module(canonical).
:- use_module(library(lists)).
:- use_module(library(sort)).

:- use_module(input_ppl).


:- dynamic(namedict/2).

main([InFile,OutFile]) :-
	load_file(InFile,pl),
    generateDict,
	open(InFile,read,In),
	open(OutFile,write,Out),
	addLocationArgs(In,Out),
	close(In),
	close(Out).
	
addLocationArgs(In,Out) :-
	read(In,C),
	(
	    C == end_of_file -> true
	;
	    addClauseArgs(C,Out),
	    addLocationArgs(In,Out)
	).
	
addClauseArgs(C,Out) :-
	addArgs(C,C1),
	!,
	write(Out,C1),
	write(Out,'.'),
	nl(Out).
addClauseArgs(_,_).
	


addArgs(C,(L1 :- R1,Z1=A1,Z2=A2,Cs)) :-
	transitionClause(C,L,Cs,R),
	!,
	L =.. [PL|Xs],
	R =.. [PR|Ys],
	getLocArgNum(PL,A1),
	getLocArgNum(PR,A2),
	append(Xs,[Z1],Xs1),
	append(Ys,[Z2],Ys1),
	L1 =.. [PL|Xs1],
	R1 =.. [PR|Ys1],
	numbervars((L1 :- R1,Z1=A1,Z2=A2,Cs),0,_).
addArgs(C,(L1 :- Z1=A1,Cs)) :-
	initialStateClause(C,L,Cs),
	L =.. [PL|Xs],
	getLocArgNum(PL,A1),
	append(Xs,[Z1],Xs1),
	L1 =.. [PL|Xs1],
	numbervars((L1 :- Z1=A1,Cs),0,_).

getLocArgNum(P,A) :-
	%name(P,Chars),
	%append(_,[95|Num],Chars),
	%\+ member(95,Num),
	%name(A,Num).
	namedict(P,A).




initialStateClause((H:-B),H,Cs) :-
	!,
	conj2list(B,Bs),
	separate_constraints(Bs,Cs1,[]),
	list2conj(Cs1,Cs).
initialStateClause(H,H,true) :-
	H =.. [P|_],
	P \== ':-',
	!.

transitionClause((H:-B),H,Cs,R) :-
	conj2list(B,Bs),
	separate_constraints(Bs,Cs1,[R]),
	list2conj(Cs1,Cs).
	
separate_constraints([],[],[]).
separate_constraints([B|Bs],[C|Cs],Ds):-
	constraint(B,C),
	!,
	separate_constraints(Bs,Cs,Ds).
separate_constraints([B|Bs],Cs,[B|Ds]):-
	separate_constraints(Bs,Cs,Ds).

constraint(false, 0<0).
constraint(true, 0 >= 0).
constraint(X=Y, X=Y).
constraint(X=:=Y, X=Y).
constraint(X is Y, X = Y).
constraint(X>Y, X>Y).
constraint(X>=Y, X>=Y).
constraint(X=<Y, X=<Y).
constraint(X<Y, X<Y).

constraint(_\==_,0=0).
constraint(_=\=_,0=0).
constraint(true,0=0).
constraint(fail,1=0).

conj2list((C,Cs),[C|Cs2]) :-
	!,
	conj2list(Cs,Cs2).
conj2list(C,[C]).

list2conj([C],C) :-
	!.
list2conj([C|Cs],(C,Ds)) :-
	!,
	list2conj(Cs,Ds).

generateDict :-
    retractall(namedict(_,_)),
	findall(P,(my_clause(H,_),functor(H,P,_)),Ps),
	sort(Ps,Qs),
	writeDict(Qs,1).
	
writeDict([Q|Qs],K) :-
	assert(namedict(Q,K)),
	K1 is K+1,
	writeDict(Qs,K1).
writeDict([],_).