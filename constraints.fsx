// Constraint type.
// The label denotes type.
// The right hand side denotes the tail nodes
type Constraint =
    | Eq  of int
    | Neq of int
    | Sum of int list
// BinaryConstraint is an incomplete active pattern match. Supplying a domain (set) to
// creates a partial active pattern match which returns the constraint predicate and node
// for a binary constraint.
let (|BinaryConstraint|_|) constrainedDomain =
    function
    | Eq  x -> ((fun value -> Set.contains value constrainedDomain),x) |> Some
    | Neq x -> ((fun value -> Set.exists ((<>) value) constrainedDomain),x) |> Some
    | _     -> None
    
// BinaryConstraint is an incomplete active pattern match. Supplying a domain (set) to
// creates a partial active pattern match which returns the constraint predicate and nodes
// for a N-ary constraint.
let (|NaryConstraint|_|) constrainedDomain =
    function
    | Sum l -> ((fun argLst -> Set.contains (List.reduce (+) argLst) constrainedDomain),l) |> Some
    | _     -> None
// Returns a list of domains associated with the given nodes
let ConstrainingDomains graph nodeNums =
    nodeNums
    |> List.map (fun n -> Map.find n graph
                          |> function
                             | dmn,_ -> dmn)
// Finds nodes that constrain node [nodeNum]
let constrainingNodes graph nodeNum =
    let constraintArgs =
        function
        | Eq  x
        | Neq x -> [x]
        | Sum l -> l
    match Map.tryFind nodeNum graph with
    | Some (_,constrs) -> Set.toList constrs
                          |> List.collect constraintArgs
    | None -> []

// ConstraintGraph type: each element of the map represents a node and its constraints
// with respect to other nodes in the map. The first Set defines the the domain of values
// the node can take and the Constraint Set is a Set of all the constraints placed on the
// node.
type Node<'a when 'a:comparison> =
    ('a Set * Constraint Set)
type ConstraintGraph<'a when 'a:comparison> =
    Map<int,Node<'a>>

// Adds a constraint to the constraint map of a node
let addConstraintToNode constr node =
    match node with
    | dmn, constrSet -> Set.add constr constrSet
                        |> fun c -> (dmn , c)
// Sets the domain of the value of a node
let setDomain graph n domain =
    match Map.tryFind n graph with
    | Some (_, constrSet) -> (domain, constrSet)
    | None                -> (domain, Set.empty)
    |> (fun node -> Map.add n node graph)

// Builds a ConstraintGraph type from a list of constraints (constrs)
// and an ordered list of domains for nodes in the graph (nodeDomains)
// This function returns an Error if the inputs are inconsistent
// (not enough domains) else it returns and Ok result.
// - constrs : A list of (int * Constraint) where the int indicates
//             the node it applies to
// - nodeDomains: A list of domains for the value of each node. E.g.
//                The domain of node 6 is nodeDomains.[6]
// N.B. Nodes are numbered from 0..(length of nodeDomains - 1)
let constraintGraphBuild constrs nodeDomains =
    // Check number of nodes is consistent
    let enoughDomains = [for (n,constr) in constrs do yield n]
                        |> List.max
                        |> (>) (List.length nodeDomains)

    // Folder to add a node constraint to a node constraintGraph
    let foldToMap map (node,constr) =
        match (Map.tryFind node map) with
        | Some n -> n
        | None   -> (Set.empty, Set.empty)
        |> addConstraintToNode constr
        |> (fun N -> Map.add node N map)

    // Function to build graph. (Takes unit so we can calculate after
    // consistency check)
    // Sorry for double back pipe
    let buildGraph():ConstraintGraph<'nodeValue> =
        constrs
        |> List.fold foldToMap Map.empty
        |> (fun m -> List.fold2 setDomain m) <|| (List.indexed nodeDomains |> List.unzip)

    // Build graph if inputs are consistent
    if enoughDomains
    then buildGraph() |> Ok
    else Error "Not enough node domains"

//Gives all choices for a list of domains
let choiceFromDomains dmnLst =
    let folder acc el =
        Set.toList el
        |> List.allPairs acc
        |> List.map (fun (a,b)->b::a)
    List.fold folder [[]] dmnLst
    |> List.map List.rev                //The lists must be reversed to respect argument order

// Returns allowable domains for tail nodes based off a predicate representing an N-ary
// constraint
let unaryFromNaryConstr domain graph constrPred constrNodes =
    // Function to take the transpose of a list list
    let rec listTranspose lst =
        match lst with
        | [] -> failwith "huh?"
        | []::x -> [] 
        | hd::tl -> (List.map List.head lst) :: listTranspose (List.map List.tail lst)
    // Function to combine a list of allowable domains into a map
    let mergeDomains nodeLst domains =
        let folder acc n dmn =
            match Map.tryFind n acc with
            | Some oldDomain -> Set.intersect dmn oldDomain //This shouldn't happen?
            | None           -> dmn
            |> (fun d -> Map.add n d acc)
        List.fold2 folder Map.empty nodeLst domains
        
    constrNodes                         
    |> ConstrainingDomains graph        // Get domains of tails nodes.
    |> choiceFromDomains                // Get all choice sets of values for these nodes.
    |> List.filter constrPred           // Filter out all illegal choice sets.
    |> listTranspose                    // Get list of leftover (allowable) domains for
                                        // each node.
    |> List.map Set.ofList              // Convert these to sets.
    |> mergeDomains constrNodes         // Create map containing calculated domains.

// Returns the allowable domain for a tail node based off a predicate representing a
// binary constraint
let unaryFromBinaryConstr domain graph constrPred constrNode =
    Map.find constrNode graph
    |> function
       | dmn,_ -> (constrNode,  Set.filter constrPred dmn)
       
let rec setDomainArcConsistent  graph n domain =
    match Map.tryFind n graph with
    | Some (oldDomain, constrSet) ->
        if oldDomain <> domain
        then Map.add n (Set.intersect oldDomain domain, constrSet) graph
             |> (fun g -> makeArcConsistent g n)
        else graph
    | None ->
        failwithf "Node %d doesn't exist" n
// Checks arc consistency started at node 'nodeNum'. This checks binary and N-ary
// constraints with different functions.
and makeArcConsistent (graph:ConstraintGraph<'a>) nodeNum:ConstraintGraph<'a> =
    // Combines unary constraints from two domain maps, m1 and m2
    let intersectDomainMaps m1 m2 =
        let folder acc n dmn  =
            match Map.tryFind n acc with
            | Some domain -> Set.intersect domain dmn
            | None        -> dmn
            |> (fun d -> Map.add n d acc)
        Map.fold folder m1 m2
    // Updates domainMap with unary constraints from domainLst
    let intersectDomains domainLst domainMap =
        let folder map (n,dmn) =
            match Map.tryFind n map with
            | Some oldDomain -> Set.intersect dmn oldDomain
            | None           -> dmn
            |> (fun d -> Map.add n d map)
        List.fold folder domainMap domainLst
    // Get head node's domain and constraints
    let (domain,constrSet) =
        match Map.find nodeNum graph  with
        | dmn,constrs -> dmn, constrs
    // Complete partial active pattern matches with head node's domain
    let (|BConstraint|_|),(|NConstraint|_|) =
        (|BinaryConstraint|_|) domain, (|NaryConstraint|_|) domain
    // Split binary and N-ary constraints into two lists
    let segregateConstraints cSet =
        let folder (binary,nary) el =
            match el with
            | BConstraint constrAndNode -> constrAndNode::binary, nary
            | NConstraint constrAndNode -> binary, constrAndNode::nary
            | _                         -> failwith "huh?"
        Set.fold folder ([],[]) cSet
           
    constrSet
    |> segregateConstraints             // Separate binary and N-ary constraints.
    |> function                         // Get unary constraints.
        | bLst, nLst ->
            List.map ((<||) (unaryFromBinaryConstr domain graph)) bLst
            ,
            List.map ((<||) (unaryFromNaryConstr domain graph)) nLst
            |> List.fold intersectDomainMaps Map.empty 
    ||> intersectDomains                     // Combine into one unary constraint map.
    |> Map.fold setDomainArcConsistent graph // Update graph with unary constraints.
                                             // This recursively call arc constraints.
                                             // This fold could be improved to reduce
                                             // superfluous operations?


// Splits graph into a list of disconnected graphs so they can be solved independently
let rec disjointGraphs (constrGraph:ConstraintGraph<'a>):ConstraintGraph<'a> list =

    // Finds all nodes connected to node returning the connected nodes
    // and a graph with those nodes removed
    let connectedNodes graph collectedNodes node =
        let rec connectedNodes' graph collectedNodes nodeLst =
            match nodeLst with
            | node::tl ->
                let constrNodes =
                    constrainingNodes graph node
                let newGraph =
                    Map.remove node graph
                connectedNodes' newGraph (node::collectedNodes) (constrNodes @ tl)
            | [] -> (graph, collectedNodes)
        connectedNodes' graph [] [node]

    // Splits graph returning a list of lists. Each list contains the
    // nodes in one connected graph
    let rec splitGraph graph disjointLst =
        Map.toList graph
        |> List.map (fun (a,_) -> a)
        |> function
           | hd::tl -> connectedNodes graph [] hd
                       |> function
                          | newGraph , collectedNodes ->
                              splitGraph newGraph (collectedNodes::disjointLst)
           | []     -> disjointLst

    // Mapper to recreate a graph from a list of it's nodes and graph
    // original graph
    let selectNodes graph nLst =
        let folder map n =
            Map.add n (Map.find n graph) map
        List.fold folder Map.empty nLst

    // Body of function
    splitGraph constrGraph [[]]
    |> List.map (selectNodes constrGraph) 

// Tests
let constrs =
    [
        (0,Eq 1)
        (1,Neq 2)
    ]

let binaryDomain = Set.ofList [0;1]
let nodeDomains = List.replicate 4 binaryDomain

let graph = constraintGraphBuild constrs nodeDomains
            |> function
               | Ok g -> g
               | Error str -> failwithf "%s" str
let test = setDomain graph 0 (Set.ofList [0])
let result = makeArcConsistent test 0;;
