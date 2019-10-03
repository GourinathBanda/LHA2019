:- module(predecessorTable,_).

:- use_module(amc). 
:- use_module(predExists_predForall2).
:- use_module(input_ppl).
:- use_module(library(ppl)).

:- use_module(canonical).
:- use_module(setops).

:-dynamic(version/3).

makePredTable(Table) :-
	findall((S,V),(version(S,_,_),predExists([S],V)), Table).

go(File,VersionsFile,Table) :-
	ppl_initialize,
	ppl_version(_),
	load_file(File,pl),
	readVersions(VersionsFile),
	makePredTable(Table),
	ppl_finalize.
	
go2(File,VersionsFile,ComplTable) :-
	ppl_initialize,
	ppl_version(_),
	load_file(File,pl),
	readVersions(VersionsFile),
	makeComplPredTable(ComplTable),
	ppl_finalize.

	
		
makeComplPredTable(Table) :-
 	findall((S,V),complPredExists(S,V), Table).
 
complPredExists(VersionId,NonSuccessors) :-
 	version(VersionId,_,ConstrList),
 	numbervars(ConstrList,0,_),
	%list2tuple(ConstrList,ConstrTuple),
	makePolyhedron(ConstrList,Handle),
	getVars(Xs),
	predExists_predForall2:predExists(Handle,Xs,PredConstrTuples),
	predExists_predForall2:negCon(PredConstrTuples,ComplementConstrTuples),
	alpha(ComplementConstrTuples,NonSuccessors).

goConcretePredExists(VersionTransitionSystemFile, VersionsFile, InVersionId, ExistsSuccessorVersionIds) :-	
	ppl_initialize,
	ppl_version(_),
	load_file(VersionTransitionSystemFile,pl),
	readVersions(VersionsFile),
	concretePredExists(InVersionId,ExistsSuccessorVersionIds),
	ppl_finalize.

concretePredExists(VersionId,ExistsSuccessorVersionIds) :-
	version(VersionId,_,ConstrList),
	numbervars(ConstrList,0,_),
	makePolyhedron(ConstrList,Handle),
	getVars(Xs),
	predExists_predForall2:predExists(Handle,Xs,PredExistsConstrTuples),
	alpha(PredExistsConstrTuples,ExistsSuccessorVersionIds).

goConcretePredForall(VersionTransitionSystemFile, VersionsFile, InVersionId, ForallSuccessorVersionIds) :-	
	ppl_initialize,
	ppl_version(_),
	load_file(VersionTransitionSystemFile,pl),
	readVersions(VersionsFile),
	concretePredForall(InVersionId,ForallSuccessorVersionIds),
	ppl_finalize.

concretePredForall(VersionId,ForallSuccessorVersionIds) :-
	version(VersionId,_,ConstrList),
	numbervars(ConstrList,0,_),
	makePolyhedron(ConstrList,Handle),
	getVars(Xs),
	predExists_predForall2:predForall(Handle,Xs,PredForallConstrTuples),
	alpha(PredForallConstrTuples,ForallSuccessorVersionIds).
	