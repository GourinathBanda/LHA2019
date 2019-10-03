:-module(predExistsTable_gnb,_).


:- use_module(input_ppl).
:- use_module(library(ppl)).


:- dynamic(version/3).
:- use_module(library(lists)).
:- use_module(predExists_predForall2).

go(File,VersionsFile) :-
	atom_concat(FileNameWithPath,'.spec',File), %gnb%
	atom_concat(FileNameWithPath,'.predExistsTable',PredTableFile), %gnb%
	ppl_initialize,
	ppl_version(_),
	load_file(File,pl),
	readVersions(VersionsFile),
	% writePredTable, %rem GNB%
	writePredTable(PredTableFile), %gnb%
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
	
allStates(Ss) :-
	setof(S,[F,C]^version(S,F,C),Ss).
	

getVars(Xs) :-
	version(_,F,_),
	numbervars(F,0,_),
	!,
	F =.. [_|Xs].

%removed GNB **********%		
%writePredTable:-
%	open('predversions.out',write,S),
%	allStates(Vs),
%	makePredTable(Vs,S),
%	close(S).
%**********************%


writePredTable(PredTableFile) :- %added this GNB%
	open(PredTableFile,write,S),
	allStates(Vs),
	makePredTable(Vs,S),
	close(S).
	
makePredTable([V|Vs],S) :-
	version(V,F,C),
	numbervars((F,C),0,_),
	getVars(Xs),
	makePolyhedron(C,H1),
	predExists(H1,Xs,Gs),
	write(S,predExistsVersion(V,Gs)),
	write(S,'.'),
	nl(S),
	makePredTable(Vs,S).
makePredTable([],_).
	

