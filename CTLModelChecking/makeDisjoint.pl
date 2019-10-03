:-module(makeDisjoint,_).



:- dynamic(version/3).
:- use_module(library(lists)).
:- use_module(library(ppl)).


% Test call
% ?- go('Tests/versions.out',R).

main([File]) :-
	go(File,_).

go(File,Regions) :-
	ppl_initialize,
	ppl_version(_),
	readVersions(File),
	findall(V,version(V,_,_), Versions),
	makeDisjoint(Versions, Regions),
	name(File,FileName),
	append(FileName,".disjoint",DisjFileName),
	name(DisjFile,DisjFileName),
	open(DisjFile,write,S),
	writeDisjointVersions(Regions,S),
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
	
makeDisjoint(Versions, DVersions) :-
	checkIntersections(Versions, Graph,[]),
	connectedSets(Graph,Versions,DVersions).
	
checkIntersections([],G,G).
checkIntersections([S|Ss],G0,G2) :-
	versionIntersect(Ss,S,G0,G1),
	checkIntersections(Ss,G1,G2).
	
versionIntersect([T|Ss],S,[S-T,T-S|G0],G1) :-
	consistentVersions(S,T),
	!,
	versionIntersect(Ss,S,G0,G1).
versionIntersect([_|Ss],S,G0,G1) :-
	versionIntersect(Ss,S,G0,G1).
versionIntersect([],_,G,G).

consistentVersions(S,T) :-
	version(S,H1,C1),
	version(T,H2,C2),
	numbervars((H1,C1),0,_),
	numbervars((H2,C2),0,_),
	append(C1,C2,C3),
	satisfiable(C3,_).
	
	
% starting from a list of vertices and links,
% make an adjacency list representation of the graph 

makeGraph(Es,Vs,G) :-
	insertVertices(Vs,G0),
	makeGraph1(Es,G0,G).
	
makeGraph1([],G,G).
makeGraph1([A-B|Ls],G0,G2) :-
	insert_succ_link(G0,A,B,G1),
	makeGraph1(Ls,G1,G2).
	
insertVertices([],[]).
insertVertices([V|Vs],[V-[]|Ws]) :-
	insertVertices(Vs,Ws).

insert_succ_link([A-Ls|G],A,B,[A-[B|Ls]|G]) :-
	!.
insert_succ_link([A1-Ls|G0],A,B,[A1-Ls|G1]) :-
	insert_succ_link(G0,A,B,G1).

% depth-first search of graph to find connected regions

connectedSets(Graph,Versions,Regions) :-
	makeGraph(Graph,Versions,G1),
	startDfs(G1,Regions).

dfs([A|Stack],G,Regions,Region,Marked) :-
	processNode(A,Stack,G,Regions,Region,Marked).
dfs([],G,Regions,Region,Marked) :-
	restartDfs(G,Regions,Region,Marked).
	
startDfs([],[]).
startDfs([A-Ls|G],Regions) :-
	dfs([A],[A-Ls|G],Regions,[],[]).
	
restartDfs([],[R],R,_).
restartDfs([A-Ls|G],[R|Regions],R,Marked) :-
	dfs([A],[A-Ls|G],Regions,[],Marked).

processNode(Top,Stack,G,Regions,Region,Marked) :-
	member(Top,Marked),
	!,
	dfs(Stack,G,Regions,Region,Marked).
processNode(A,Stack,G,Regions,Region,Marked) :-
	removeNode(G,A,Ls,G1),
	append(Ls,Stack,NewStack),
	dfs(NewStack,G1,Regions,[A|Region],[A|Marked]).
	
removeNode([A-Ls|G],A,Ls,G) :-
	!.
removeNode([N|G0],A,Ls,[N|G1]) :-
	removeNode(G0,A,Ls,G1).
	
satisfiable(Cs,H1) :-
	ppl_new_NNC_Polyhedron_from_constraints(Cs,H1),
	\+ ppl_Polyhedron_is_empty(H1).
	
writeDisjointVersions([[V]|Rs],S) :-
	!,
	version(V,H,C),
	numbervars((H,C),0,_),
	write(S,version(V,H,C)),
	write(S,'.'),
	nl(S),
	writeDisjointVersions(Rs,S).
writeDisjointVersions([[V|Vs]|Rs],S) :-
	version(V,H1,C1),
	numbervars((H1,C1),0,_),
	findall((H,C),(
		member(W,Vs),
		version(W,H,C),
		numbervars((H,C),0,_)), 
	  Cs),
	write(S,'version('),
	write(S,V),
	write(S,','),
	write(S,H1),
	write(S,',('),
	nl(S),
	writeAllRegions([(H1,C1)|Cs],S),
	write(S,')).'),
	nl(S),
	writeDisjointVersions(Rs,S).
writeDisjointVersions([],_).

writeAllRegions([(_,C)],S) :-
	!,
	write(S,'      '),
	write(S,C).
writeAllRegions([(_,C)|Cs],S) :-
	write(S,'      '),
	write(S,C),
	write(S,';'),
	nl(S),
	writeAllRegions(Cs,S).

	