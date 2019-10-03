:-module(refineProp,_).



:- dynamic(version/3).
:- dynamic(splitversion/3).

:- use_module(library(lists)).
:- use_module(library(ppl)).



% Test call
% ?- go('Tests/versions.out',R).

go(File,C, Xs,OutFile) :-
	ppl_initialize,
	ppl_version(_),
	readVersions(File),
	retractall(splitversion(_,_,_)),
	negate(C,Ns),
	split([C|Ns],Xs),
	open(OutFile,write,S),
	writeSplitVersions(S),
	close(S),
	ppl_finalize.

readVersions(File) :-
	retractall(version(_,_,_)),
	open(File,read,S),
	readVersionFacts(S),
	close(S).
	
readVersionFacts(S) :-
	read(S,C),
	(
	    C == end_of_file -> true
	;
	    assert(C),
	    readVersionFacts(S)
	).
	
negate(X=Y,[X>Y,Y>X]).
negate(X>=Y,[X<Y]).
negate(X>Y,[X=<Y]).
negate(X=<Y,[X>Y]).
negate(X<Y,[X>=Y]).

split(Rs,Xs) :-
	version(L,H,Cs),
	H =.. [_|Xs],
	addEachConstraint(Rs,L,H,Cs,0),
	fail.
split(_,_).
	

addEachConstraint([],_,_,_,_) :-
	!.
addEachConstraint([R|Rs],L,H,Cs,K) :-
	\+ \+ checkSat([R|Cs]),
	!,
	versionNumber(L,K,L1),
	assert(splitversion(L1,H,[R|Cs])),
	K1 is K+1,
	addEachConstraint(Rs,L,H,Cs,K1).
addEachConstraint([_|Rs],L,H,Cs,K) :-
	addEachConstraint(Rs,L,H,Cs,K).
	
checkSat(Cs) :-
	numbervars(Cs,0,_),
	satisfiable(Cs,_).

satisfiable(Cs,H1) :-
	ppl_new_NNC_Polyhedron_from_constraints(Cs,H1),
	\+ ppl_Polyhedron_is_empty(H1).

writeSplitVersions(S) :-
	splitversion(L,H,Cs),
	numbervars(splitversion(L,H,Cs),0,_),
	write(S,version(L,H,Cs)),write(S,'.'), nl(S),
	fail.
writeSplitVersions(_).

versionNumber(L,K,L1) :-
	name(L,S1),
	name(K,S2),
	append(S1,[95|S2],S3),
	append("v",S3,S4),
	name(L1,S4).
