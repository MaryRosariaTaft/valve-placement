/* Program that solves the valve placement problem described in
    MASSIMILIANO CATTAFI, MARCO GAVANELLI, MADDALENA NONATO, STEFANO ALVISI and MARCO FRANCHINI
    Optimal Placement of Valves in a Water Distribution Network with CLP(FD)
    27th International Conference on Logic Programming ICLP 2011

Written by Massimiliano Cattafi and Marco Gavanelli

Tested with ECLiPSe (http://eclipseclp.org/) Version 6.0 #169 on Linux

Usage: 
- provide an instance of a network (see file apulian.pl for an example)
- invoke predicate p/4 (see comments below for an example)

    
*/


:- lib(fd).
:- lib(fd_global).
:- lib(fd_search).
:- lib(graph_algorithms).
:- lib(listut).
:- lib(var_name).
:- import append/3 from eclipse_language.
:- import delete/3 from eclipse_language.
:- import sumlist/2 from fd_global.

:- set_event_handler(280, found_solution/2).

:- dynamic counter/1.
:- dynamic initial_time/1.
:- dynamic broken_sector/1.


counter(0).

increment:-
    (retract(counter(C))
        ->    C1 is C+1
        ;   C1 is 1
    ),
    assert(counter(C1)).

% handler invoked whenever the branch-and-bound finds a better solution,
% instead of the default one that prints "Found a solution with cost ..."
found_solution(280,(V,G)):-
    (G=(max_member_sort(_,_),_) % If we are in the internal minimize, don't print anything
        -> true
        ;   write(V), write('\t'), cputime(Now), initial_time(Inizio), Delta is Now-Inizio,
            writeln(Delta)
    ).

% main goal: NV is the Number of Valves to put in the network
q(NV):- p(_,NV,_,_), retract(counter(X)), writeln(explored_nodes(X)).

% p(+G,+NV,-Vv,-Cost)
% Given
% - a graph G
% - a number of valves NV
% provides the best assignment of valves (Vv) and the corresponding Cost
% Vv is a list of 0-1 variables:
% 0 means no valve in such position
% 1 means a valve is in such position
p(_,_,_,_):- not(current_predicate(network_nn_edges/2)),!,
    writeln("*** ERROR: NO INSTANCE LOADED ***"),
    writeln("compile file apulian.pl as an example").
p(G,NV,Vv,Cost) :-
    network_nn_edges(NN,Edges1), % consider the edges (Edges1) of the graph in the instance, and the number of nodes (NN)
    add_valves_undirected(Edges1, [], Edges), % adds the necessary information to the edges of the graph
    make_graph(NN, Edges, G), % creates the graph
        
    cputime(CPUtime),
    retractall(initial_time(_)),
    assert(initial_time(CPUtime)), % Saves the value of the CPU time
    
    pipe_water(G,TPD), % Computes (twice) the sum of the weights of the edges in a graph: TPD is the total weight
    arg(2, G, Gedges),
    Gedges =.. EdgesLoL, % rearrange the edges in a List of Lists (EdgesLoL)
    get_arg_in_multilist(EdgesLoL,[3,1],Vv), % Extracts the decision variables in the list Vv
    occurrences(1, Vv, NV), % Imposes that there are exactly NV valves in the network

    % REDUNDANCY BLOCK 1 OF 2 ======================
    find_all_minimal_cycles(G, MCycles), % Finds the minimal cycles (faces boundaries) in the network
    
    (foreach(Cycle, MCycles), param(Gedges) do
    % impose constraints on faces
        get_arg_in_multilist(Cycle,[3,1],VCycle),
        dual_cycle(Gedges, Cycle, DCycle),
        get_arg_in_multilist(DCycle,[3,1],VDCycle),
        append(VCycle,VDCycle,AllCycle),
        occurrences_not_eq(AllCycle,1) % In each cycle, there cannot be 1 valve
    ),
    % ================== END REDUNDANCY BLOCK 1 OF 2

    arg(1, Gedges, GedgesS),
    get_arg_in_multilist(GedgesS,[3,1],GedgesSV),
    GedgesSV::1, % Put a valve in all arcs outgoing from the source of water

    % REDUNDANCY BLOCK 2 OF 2 ======================
    (for(I, 2, NN), param(Gedges) do
        arg(I, Gedges, NEdges),
        get_arg_in_multilist(NEdges,[3,1],VNEdges),
        (VNEdges=[X,_] -> X=0 ; true) % symmetry breaking: if a node has exactly 2 outgoing edges, there is no point in adding two valves, and they are symmetric
    ),
    % ================== END REDUNDANCY BLOCK 2 OF 2
    
    set_var_name(SegC,"SegC"), % Sets the variable names for debugging purposes
    set_var_name(NegSegC,"NegSegC"),
    Cost+SolNegSegC#=0,
    set_var_name(Cost,"Cost"),
    set_var_name(SolNegSegC,"SolNegSegC"),

    flatten(EdgesLoL,EdgesList), % List of edges with all the data: e(Node1,Node2,vs(ValveVariable,_,_))

    swap_edgeslist(EdgesList,SwappedEdgesList),

    % LOWER BOUND BLOCK ============================
    impose_lower_bound_constraint(EdgesLoL,Gedges,Cost),
    % ======================== END LOWER BOUND BLOCK
    
    no_two_valves_same_arc(EdgesList),

        minimize( 
            (
                labeling_edges_symm(SwappedEdgesList),
                increment, % Increments number of visited nodes in the search tree; will be printed at the end of the search
                
                sectors(NN, Edges, Sec1), % Compute the sectors
                once(delete([1], Sec1, Sec)), % remove from the set of sectors the sector containing only the source node
                
                sec_dem_pipe(Cost, G, Sec, Sec2LL),
                minimize_bound_check, % Updates the value of the bound for the objective function
                mindomain(SolNegSegC,Lower),
                minimize(
                    (                        
                        max_member_sort(BrSL, Sec2LL), % Choose nondeterministically one sector to break, starting from the biggest one
                        BrSL = seclen(BrS, _), % Consider the list of nodes in the chosen sector
                        
                        SegC+NegSegC#=0, % Negate the objective function in order to compute the maximum (in ECLiPSe there is no maximize predicate)
                        break_seg_sups(G, [BrS], [SegC1]), % Break sector BrS and obtain its delivered demand SegC1

                        SegC is TPD - SegC1 
                    ),
                    (BSec,NegSegC,BrS),    % template
                    (SolBSec,SolNegSegC,_),    % solution
                    NegSegC,  % cost
                    Lower, % lower
                    +10000, % upper
                    0,  % percent
                    0   % timeout
                ),
                BSec=SolBSec
            ),
            Cost
    ),
    ActualCost is Cost/20,
    writeln(actual_cost(ActualCost)).

% Rearranges the edges such that the two valves on the same edge are one after the other in the list
swap_edgeslist([],[]).
swap_edgeslist([H|T],[H,Back|T1]):-
    H=e(S,D,_),Back=e(D,S,_),
    once(delete(Back,T,Rest)),
    swap_edgeslist(Rest,T1).

% get_arg_in_multilist(+MultiList,++ArgList,-OutList)
% MultiList is a list of lists of lists ...
% ArgList is a list of indices
% OutList is a list of elements identified by the ArgList
% E.g., get_arg_in_multilist([ [A,B,C], [D,E,F], [G,H,I] ], [2], OutList)
% provides in OutList a list containing the second element of each of the lists, i.e.: [B,E,H]
get_arg_in_multilist([],_,[]).
get_arg_in_multilist([H|T],ArgList,OutList):-
    H=[_|_],!,
    get_arg_in_multilist(H,ArgList,Out1),
    get_arg_in_multilist(T,ArgList,Out2),
    append(Out1,Out2,OutList).
get_arg_in_multilist([[]|T],ArgList,OutList):- !,
    get_arg_in_multilist(T,ArgList,OutList).
get_arg_in_multilist([H|T],ArgList,[El|OutList]):-
    multi_arg(ArgList,H,El),
    get_arg_in_multilist(T,ArgList,OutList).

% A generalization of the arg/3 predicate of Prolog
% Like arg/3, but takes l list of indices instead of a single index
% multi_arg([1,2,3],p(q(_,r(_,_,s))),El) returns El=s,
% because it considers the first parameter of term p (that is q)
% the second argument of q, and the third of s
multi_arg([],X,X).
multi_arg([I|T],Term,El):-
    arg(I,Term,X),
    multi_arg(T,X,El).

% Imposes that there cannot be two valves on the same edge
% (same assumption as Giustolisi and Savic)
no_two_valves_same_arc([]).
no_two_valves_same_arc([e(S,D,Data)|ArcList]):-
    once(delete(e(D,S,DataBack),ArcList,Rest)),
    arg(1,Data,Var1), arg(1,DataBack,Var2),
    minlist([Var1,Var2],0),
    no_two_valves_same_arc(Rest).

% occurrences_not_eq(+BoolList,++Num)
% BoolList is a list of variables with domain [0..1]
% Imposes that the number of elements equal to 1 in BoolList is different from Num
occurrences_not_eq([X],0):-!, X=1.
occurrences_not_eq([X],1):-!, X=0.
occurrences_not_eq(_,N):- N<0, !.
occurrences_not_eq([H|T],N):-
    nonvar(H),!,
    (H=1 -> N1 is N-1, occurrences_not_eq(T,N1)
        ;   occurrences_not_eq(T,N)
    ).
occurrences_not_eq([H|T],N):-
    suspend(occurrences_not_eq([H|T],N),1,H->inst).
    
dual_cycle(GEdges, Cycle, DualCycle):-
     (foreach(Arc, Cycle), foreach(DArc, DualCycle), param(GEdges) do
        Arc = e(S,D,_),
        arg(D,GEdges,DArcs),
        memberchk(e(D,S,VS), DArcs),
        DArc = e(D,S,VS)
    ).
  
sectors(NN, Edges, Sec) :-
    remove_v_edges(Edges, [], Edges2), % Remove the arcs containing a valve
    make_graph(NN, Edges2, G2), % Create a graph without such edges
    connected_components(G2, Sec). % compute the connected components of the graph

remove_v_edges(Edges, Acc, Edges2) :-
    (Edges==[] ->
        Acc=Edges2
    ;
        Edges=[HEdges | TEdges],
        arg([3,1], HEdges, HEV),
        HEdges = e(S,D, _),
        once(delete(e(D,S, VSBack), TEdges, TEdges1)),
        arg(1,VSBack,ValveBack),
        ((HEV == 1 ; ValveBack==1)
            -> % is there a valve?
                remove_v_edges(TEdges1, Acc, Edges2)
            ;   Acc1=[HEdges,e(D,S, VSBack)|Acc],
                remove_v_edges(TEdges1, Acc1, Edges2)
        )
    ).




add_valves_undirected(E1, Acc, E2) :- 
    (E1 == [] -> 
        Acc = E2
    ;
        E1 = [HE1 | TE1],
        HE1 = e(S,D,Sup),
        _V1::0..1,
        _V2::0..1,
        F1 #>=0, F2 #>=0,
        NE1 = e(S, D, vs(_V1, Sup,F1)),
        NE2 = e(D, S, vs(_V2, Sup,F2)),
        add_valves_undirected(TE1, [NE1, NE2 | Acc], E2)
    ).

% Given a list of sectors Sec (each sector is a list of nodes)
% provides in the list Sups the serviced demand when each of the sectors is excluded
% (for each sector, provides its cost, including unintended isolations)
break_seg_sups(Graph, Sec, Sups) :-
    arg(1, Graph, NNodes),
    arg(2, Graph, Edges),
    (foreach(Sector, Sec), foreach(Sup, Sups), param(Graph, NNodes, Edges) do
        make_sublist(NNodes, Sector, SLSector),	% Compute the set of nodes not belonging to Sector
        make_sub_graph(Graph, SLSector, SLGraph), % Compute the sub-graph consisting only of the nodes in Sector
        connected_components(SLGraph, ConnSLGraph), % Find the connected components
        node2sector(1, ConnSLGraph, ConnSec),	% Consider the component containing node 1 (the source)
        pipes_sups(ConnSec, Edges, Sup)
    ).

% pipes_sups(++Sec, +Edges, -Sup)
% Assuming that the nodes in Sec are reached by water,
% compute in Sup (twice) the total serviced demand.
pipes_sups(Sec, Edges, Sup) :-
    (foreach(Node, Sec), fromto(0, In, Out, Sup), param(Edges, Sec) do
        arg(Node, Edges, NEdges),
        pipe_node_sups(Sec, NEdges , SupN),
        Out is In + SupN
    ).

% pipe_node_sups(++Sec, +NEdges, -Sup)
% Sec is a list of nodes, reached by water.
% NEdges is a list of edges outgoing from one node (assumed to be in Sec)
% Provides in Sup the serviced demand of the edges in NEdges
pipe_node_sups(Sec, NEdges, Sup) :-
    (foreach(Edge, NEdges), fromto(0, In, Out, Sup), param(Sec) do
        Edge = e(_, D, vs(V, S,_)),
        (member(D, Sec)->
            Out is In + S   % If both nodes are serviced, add the demand of the edge.
                             % It will be added once for this edge and once for the backward edge
        ;   % If the other node D is not reached by water
            (V == 1 ->      % if there is a valve near the first node, the edge is not serviced
                Out is In
            ;               % if there is no valve near the first node, it must be on the other side of the edge, so we add the demand twice
                Out is In + S + S
            )
        )
    ).


% make_sublist(+NNodes, +Sector, -SLSector)
% Provides in SLSector the list of numbers from  1 to NNodes, excluding those appearing in the list Sector
make_sublist(NNodes, Sector, SLSector):-
    make_sublist(1,NNodes,Sector,SLSector).

make_sublist(N,N,[N],[]):-!.
make_sublist(N,N,[],[N]):-!.
make_sublist(N,Max,Rem,Out):-
    delete(N,Rem,NewRem),!, N1 is N+1, make_sublist(N1,Max,NewRem,Out).
make_sublist(N,Max,Rem,[N|Out]):- !, N1 is N+1, make_sublist(N1,Max,Rem,Out).

pipe_water(G, W) :-
    arg(2, G, Edges),
    (foreachelem(EdgeList, Edges), fromto(0, In, Out, W) do
        sum_edges(EdgeList, 0, PS),
        Out is In + PS
    ).
        

sum_edges(EdgeList, Acc, Sum) :-
    (EdgeList == [] ->
        Acc = Sum
    ;
        EdgeList = [HEdgeList | TEdgeList],
        arg([3,2], HEdgeList, W),
        Acc1 is Acc + W,
        sum_edges(TEdgeList, Acc1, Sum)
    ).
    
% node2sector(+Node, +Sectors, -S)
% Given a node and a list of sectors, provides the Sector that contains the Node
node2sector(Node, Sectors, S) :-
    Sectors = [SH | ST],
    (ST == [] ->
        S = SH
    ;
        (member(Node, SH) -> 
            S = SH
        ;
            node2sector(Node, ST, S)
        )
    ).
        
% sec_dem_pipe(?Cost, +Graph, +Sec, -Sec2)
% Given
% - the Cost variable for the whole graph
% - a Graph
% - a list of sectors (Sec)
% provides in Sec2 a list of terms seclen(Sector,SectorLenght)
% where Sector is a sector (list of nodes)
% and SectorLength is its cost
sec_dem_pipe(Cost, Graph, Sec, Sec2):-
    (foreach(Sector, Sec), foreach(SecNum, Sec2), param(Graph, Cost) do 
        make_sub_graph(Graph, Sector, Graph2), % Create a subgraph containing all the nodes except those in the Sector
        pipe_water(Graph2, SecNumLen), % Compute the sum of the weights in the subgraph
        Cost #>= SecNumLen, % The cost is always bigger than the cost of any of the sectors
        SecNum = seclen(Sector, SecNumLen)
    ).
    
max_member_sort(El,List):-
    sort(2,>=,List,Sorted),
    member(El,Sorted).
    
    
find_all_minimal_cycles(G, Cycles) :-
    arg(1, G, NN),
    graph_get_all_edges(G,Edges),
    (for(I, 1, NN), fromto([], In, Out, CyclesR), param(Edges, NN, G) do % For each node
        graph_get_adjacent_edges(G, I, AdEdges),
        node_cycles(NN, Edges, AdEdges, PCycles),
        append(In, PCycles, Out)
    ),
    remove_duplicates(CyclesR, [], Cycles).
        

node_cycles(NN, Edges, AdEdges, Cycles) :- 
    (foreach(Edge, AdEdges), foreach(Cycle, Cycles), param(NN, Edges) do
        Edge = e(S,D, _),
        once(delete(Edge, Edges, NEdges)),
        make_graph(NN, NEdges, G),                  % Creates a graph in which we remove one arc
        single_pair_shortest_path(G, 2, S, D, Path),% then finds the shortest path between the nodes connected by the removed edge
        Path = _ - PPath,
        Cycle = [Edge | PPath]                      % finally, re-adds the removed edge
    ).

remove_duplicates(ListR, Acc, List) :- 
    (ListR == [] ->
        Acc = List
    ;
        ListR = [ELR | TLR],
        (foreach(ETLR, TLR), fromto([], In, Out, NewTLR), param(ELR) do
            (no_order_equal_list(ETLR, ELR) ->
                Out = In
            ;
                Out = [ETLR | In]
            )
        ),
        Acc1 = [ELR | Acc],
        remove_duplicates(NewTLR, Acc1, List)
    ).
    

no_order_equal_list(L1, L2) :-
    (foreach(EL, L1), param(L2) do
        once(member(EL, L2))
        ;
        (
            EL = e(S,D,_),
            once(member(e(D,S,_), L2))
        )
    ).

labeling_edges_symm([]).
labeling_edges_symm([e(_,_,vs(X,_,_)),e(_,_,vs(Y,_,_))|T]):-
    indomain_max(X),
    indomain_min(Y),
    labeling_edges_symm(T).

indomain_min(0).
indomain_min(1).

indomain_max(1).
indomain_max(0).

% As explained in [Cattafi et al., ICLP 2011], for each node we need to have:
% 1. a variable representing the sector that contains the node
% 2. a Lower Bound on the size of such sector.
% The two pieces of information can also be stored in just one variable S:
% 1. S represents the sector
% 2. its domain represents the lower bound (in particular, if S :: LB..UB, the lower bound is LB)
impose_lower_bound_constraint([],_,_).
impose_lower_bound_constraint([NodeEdges|LoL],Gedges,Cost):-
% NodeEdges are edges outgoing from a same node
    (NodeEdges = []
    ->  true
    ;   % Since the graph library stores the information in arcs, while we need to associate a
        % variable to each node, we create two sector variables for each arc (one for each node of the arc), then we unify
        % the variables on a same node. This is done by predicate sector_variable
        sector_variable(NodeEdges,S), 
        Cost #>= S,
        impose_lower_bound_loop(NodeEdges,Gedges,Cost)
    ),
    impose_lower_bound_constraint(LoL,Gedges,Cost).

impose_lower_bound_loop([],_,_).
impose_lower_bound_loop([Edge|Edges],Gedges,Cost):-
    Edge = e(S,D,vs(X,C,FX)),
    S<D,!,  % Impose the constraint only once per each edge, so only when the first node has ID < second node
    arg(D,Gedges,BackList),
    memberchk(e(D,S,vs(Y,C,FY)),BackList), % Extract the edge in the opposite direction
    Weight = C,
    lower_bound(vs(X,Weight,FX),vs(Y,Weight,FY),Cost),
    impose_lower_bound_loop(Edges,Gedges,Cost).
impose_lower_bound_loop([Edge|Edges],Gedges,Cost):-
    Edge = e(S,D,_),
    S>D,
    impose_lower_bound_loop(Edges,Gedges,Cost).

lower_bound(vs(Vij,_,Si),vs(Vji,_,Sj),_Cost):-
    Si==Sj,!, Vij=0, Vji=0. % If they are already the same sector, there is no point in having a valve in between
lower_bound(vs(Vij,Weight,Si),vs(Vji,Weight,Sj),Cost):-
    var(Vij),var(Vji),!, % if none of the valve is placed, suspend
    suspend(lower_bound(vs(Vij,Weight,Si),vs(Vji,Weight,Sj),Cost),8,[Vij,Vji]->inst).
lower_bound(vs(Vij,Weight,Si),vs(Vji,Weight,Sj),Cost):- % Here we just got the information that Vji has been assigned
    var(Vij),!,
    maxdomain(Cost,MaxCost), % This is the cost of the incumbent solution: we are not going to accept anything worse
    mindomain(Si,LBi),       % This is the lower bound on the cost of the sector
    (LBi+Weight > MaxCost   % If the lower bound + cost of the arc exceeds the incumbent solution, 
        ->  Vij=1           % impose a valve
        ;   (Vji=0          % if on the opposite end there is no valve
                ->  mindomain(Sj,LBj),  % compute the current lower bound of the other sector
                    Sj #>= LBj+Weight,  % since there is no valve Vji, add the Weight of the arc to the lower bound of sector Sj
                    (LBj+LBi+Weight > MaxCost % if, by joining sectors Si and Sj we would exceed the incumbent solution
                        ->  Vij=1       % impose there is a valve in Vij
                        ;   suspend(lower_bound_one_ground(vs(Vij,Weight,Si),vs(Vji,Weight,Sj)),3,Vij->inst)
                    )
                ;   suspend(lower_bound_one_ground(vs(Vij,Weight,Si),vs(Vji,Weight,Sj)),3,Vij->inst)
            )
    ).
% The following clauses are selected if both the valves have just been assigned
% (the last time the constraint was awaken they were both variables, while now they are both ground)
lower_bound(vs(Vij,Weight,Si),vs(Vji,Weight,Sj),Cost):-
    var(Vji),!,
    lower_bound(vs(Vji,Weight,Sj),vs(Vij,Weight,Si),Cost).
lower_bound(vs(1,_,_),_,_).
lower_bound(vs(0,Weight,Si),vs(1,Weight,_),_):- 
    mindomain(Si,LBi),
    Si #>= LBi+Weight.
lower_bound(vs(0,Weight,Si),vs(0,Weight,Sj),_):-
    mindomain(Si,LBi),
    mindomain(Sj,LBj),
    Si=Sj,              % join the two sectors
    Si #>= LBi+LBj+Weight.  % update the bound: it is the sum of the two bounds+the Weight of the edge

% This constraint has the same meaning as lower_bound, but it assumes that Vji is already ground.
% In particular, when lower_bound_one_ground is awaken, it means that Vij has just been assigned
% (so, since Vji was already ground and Vij is just been assigned, this means that both are ground)
lower_bound_one_ground(vs(Vij,Weight,Si),vs(Vij,Weight,Sj)):-
    var(Vij),!, % This should never happen, we just add it to be sure that nothing wrong can happen
     suspend(lower_bound_one_ground(vs(Vij,Weight,Si),vs(Vij,Weight,Sj)),3,Vij->inst).
lower_bound_one_ground(vs(Vij,_,Si),vs(Vji,_,Sj)):-
    Si==Sj,!,Vij=0,Vji=0. % If they are already the same sector, there is no point in having a valve in between
lower_bound_one_ground(vs(1,_,_),_).
lower_bound_one_ground(vs(0,_,Si),vs(0,_,Sj)):-
    mindomain(Si,LBi), % Lower bound of sector Si
    mindomain(Sj,LBj), % Lower bound of sector Sj
    Si=Sj,              % join the two sectors
    Si #>= LBi+LBj.     % update the bound. The Weight of the node was already considered in the LBj
lower_bound_one_ground(vs(0,Weight,Si),vs(1,Weight,_)):-
    mindomain(Si,LBi),
    Si #>= LBi+Weight.

sector_variable([],_).
sector_variable([e(_,_,vs(_,_,F))|NodeEdges],F):-
    sector_variable(NodeEdges,F).


