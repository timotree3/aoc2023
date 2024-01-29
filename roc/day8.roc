## Solution to both parts of https://adventofcode.com/2023/day/8
app "day8"
    packages { pf: "https://github.com/roc-lang/basic-cli/releases/download/0.7.0/bkGby8jb0tmZYsy2hg1E_B2QrCgcSTxdUlHtETwm5m4.tar.br" }
    imports [pf.Stdout, pf.Task.{ Task }, "../inputs/day8.txt" as input : Str]
    provides [main] to pf

main : Task {} I32
main =
    {} <- Stdout.line "Part 1: \(Num.toStr (part1 (parse input)))" |> Task.await
    Stdout.line "Part 2: \(Num.toStr (part2 (parse input)))"

Direction : [Left, Right]
Node : Str
Input : { directions : List Direction, nodes : Dict Node (Node, Node) }

# Parsing

parse : Str -> Input
parse = \inp ->
    { before: directions, after: nodes } = inp |> Str.trim |> Str.splitFirst "\n\n" |> orCrash

    { directions: parseDirections directions, nodes: parseNodes nodes }

parseDirections : Str -> List Direction
parseDirections = \s ->
    s
    |> Str.toUtf8
    |> List.map parseDirection

parseDirection = \b ->
    when b is
        'L' -> Left
        'R' -> Right
        _ -> crash "expected direction to be 'L' or 'R'"

parseNodes : Str -> Dict Node (Node, Node)
parseNodes = \s ->
    s
    |> Str.split "\n"
    |> List.map parseNode
    |> Dict.fromList

parseNode : Str -> (Node, (Node, Node))
parseNode = \line ->
    { before: node, after: exits } = Str.splitFirst line " = (" |> orCrash
    { before: left, after: right } =
        exits
        |> Str.replaceEach ")" ""
        |> Str.splitFirst ", "
        |> orCrash
    (node, (left, right))

# Part 1

example1 =
    """
    RL

    AAA = (BBB, CCC)
    BBB = (DDD, EEE)
    CCC = (ZZZ, GGG)
    DDD = (DDD, DDD)
    EEE = (EEE, EEE)
    GGG = (GGG, GGG)
    ZZZ = (ZZZ, ZZZ)
    """

expect
    answer = part1 (parse example1)
    # It takes two steps to get from AAA to ZZZ by going RL:
    # R to CCC then L to ZZZ.
    answer == 2

example2 =
    """
    LLR

    AAA = (BBB, BBB)
    BBB = (AAA, ZZZ)
    ZZZ = (ZZZ, ZZZ)
    """

expect
    answer = part1 (parse example2)
    # It takes 6 steps to get from AAA to ZZZ by going LLR:
    # L to BBB, L to AAA, R to BBB, L to AAA, L to BBB, R to ZZZ
    answer == 6

part1 : Input -> Nat
part1 = \{ directions, nodes } ->
    walk startNode directions nodes 0

startNode = "AAA"
endNode = "ZZZ"

followDirection = \(left, right), direction ->
    when direction is
        Left -> left
        Right -> right

step = \node, directions, nodes, i ->
    dir = List.get directions (i % (List.len directions)) |> orCrash

    nodes
    |> Dict.get node
    |> orCrash
    |> followDirection dir

walk = \node, directions, nodes, i ->
    if node == endNode then
        i
    else
        node
        |> step directions nodes i
        |> walk directions nodes (i + 1)

# Part 2

example3 =
    """
    LR

    11A = (11B, XXX)
    11B = (XXX, 11Z)
    11Z = (11B, XXX)
    22A = (22B, XXX)
    22B = (22C, 22C)
    22C = (22Z, 22Z)
    22Z = (22B, 22B)
    XXX = (XXX, XXX)
    """

expect
    answer = part2 (parse example3)
    # It takes 6 steps to reach Zs with all cursors simultaneously starting from 11A and 22A and going LR.
    # 0: 11A and 22A
    # 1: 11B and 22B
    # 2: 11Z and 22C
    # 3: 11B and 22Z
    # 4: 11Z and 22B
    # 5: 11B and 22C
    # 6: 11Z and 22Z
    answer == 6

isStartNode = \name -> Str.endsWith name "A"
isEndNode = \name -> Str.endsWith name "Z"

## Returns the intersection of two "congruence sets" in O(nm) time
##
## A congruence set is a tuple `(s, p)` representing
## a set of possible numbers `s` which repeats with period `p`.
##
## e.g. the congruence set ({1, 2}, 4) represents the infinite set {1, 2, 5, 6, 9, 10, 13, 14, ...}
mergeCongruenceSets : (Set I64, I64), (Set I64, I64) -> (Set I64, I64)
mergeCongruenceSets = \(ms, p), (ns, q) ->
    (filterMapPairs ms ns \m, n -> congruentToBoth m p n q, lcm p q)

## Returns the the lowest n such that n % p == s and n % q == t.
congruentToBoth = \s, p, t, q ->
    dbg
        { s, p, t, q }

    # We use the formula n = ((t - s)/p mod q) * p + s
    #
    # Rationale:
    # - Let's work with the example of s = 2, p = 3, t = 3, and q = 5.
    # - We need to find an n such that n % 3 == 2 and n % 5 == 3.
    # - n = 2 satisfies the first condition.
    # - Now the question is how many 3s to we have to add to get n % 5 == 3
    # - Right now n % 5 == 2. We have to add 1 mod 5. 1/3 mod 5 = 2.
    # - Therefore we have to add 2 * 3.
    # - n = 2 + 2 * 3 = 8
    #
    # That example was simple because both p and q were prime.
    # - Now let's find an n such that n % 6 == 4 and n % 9 == 5 (impossible)
    #   - n = ((5 - 4)/6 mod 9) * 6 + 4
    #   - 1/6 mod 9 doesn't exist
    #   - We would get an error as desired
    # - Now let's find an n such that n % 6 == 4 and n % 9 == 7
    #   - n = ((7 - 4)/6 mod 9) * 6 + 4
    #   - 3/6 mod 9 = 2
    #   - 2 * 6 + 4 = 16
    #
    # Will our answer be unique mod lcm(p, q)? Yes.
    # - Is p * (n/p mod q) mod lcm(p, q) unique?
    #   - (n/p mod q) is unique mod (q/gcd(p, q))
    #     - I know this from playing modular division
    #   - p * (n/p mod q) has unique answers mod (p * q / gcd(p,q)) = lcm(p, q)
    #
    # After writing this, I found a simpler formula at https://en.wikipedia.org/wiki/Chinese_remainder_theorem#Generalization_to_non-coprime_moduli,
    # but this is the one I came up with.
    x <- divMod (t - s) p q |> Result.map
    x * p + s

expect congruentToBoth 2 3 3 5 == Ok 8
expect congruentToBoth 4 6 7 9 == Ok 16
expect congruentToBoth 0 2 1 6 == Err InvalidDivision

## The [Extended Euclidean Algorithm](https://en.wikipedia.org/wiki/Extended_Euclidean_algorithm)
xgcd : I64, I64 -> (I64, I64, I64)
xgcd = \a, b ->
    (r, s, t) = xgcdTR (Num.max a b) (Num.min a b) 1 0 0 1
    if a >= b then
        (r, s, t)
    else
        (r, t, s)

xgcdTR = \r0, r1, s0, s1, t0, t1 ->
    if r1 == 0 then
        (r0, s0, t0)
    else
        q2 = Num.divTrunc r0 r1
        r2 = r0 % r1
        s2 = s0 - (q2 * s1)
        t2 = t0 - (q2 * t1)
        xgcdTR r1 r2 s1 s2 t1 t2

expect
    answer = xgcd 240 46
    answer == (2, -9, 47)

expect
    answer = xgcd 46 240
    answer == (2, 47, -9)

## Computes the Euclidean mod. (Always returns a positive result.)
modE = \m, n ->
    r = m % n
    if r < 0 then
        r + n
    else
        r

## Computes the least solution `x` to `x * n = m (mod p)`, if any exist.
divMod : I64, I64, I64 -> Result I64 [InvalidDivision]
divMod = \m, n, p ->
    # First normalize the inputs to be between [0, p)
    mModP = m |> modE p
    nModP = n |> modE p
    # r = _s * p + t * nModP = gcd(p, nModP)
    (r, _s, t) = xgcd p nModP
    # If r divides m, n divides m as well and we have a solution.
    if mModP % r == 0 then
        # Normalize `t` to be between [0, p)
        tModP = t |> modE p
        # We have t * n = r (mod p) and therefore ((m/r) * t) * n = m (mod p)
        solution = (mModP |> Num.divTrunc r) * tModP
        # This solution is unique mod p/gcd(p, n)
        leastSolution = solution % (p |> Num.divTrunc r)
        expect (leastSolution * n) % p == mModP
        Ok leastSolution
    else
        dbg
            "\(Num.toStr mModP) / \(Num.toStr nModP) mod \(Num.toStr p) doesn't exist"

        Err InvalidDivision

expect divMod 1 1 5 == Ok 1
expect divMod 1 2 5 == Ok 3
expect divMod 1 3 5 == Ok 2
expect divMod 1 4 5 == Ok 4
expect
    answer = divMod 3 6 9
    answer == Ok 2
expect
    answer = divMod 6 6 9
    answer == Ok 1
expect
    answer = divMod 98 4 102
    answer == Ok 50

gcd = \a, b ->
    (r, _s, _t) = xgcd a b
    r

lcm = \a, b -> a * b |> Num.divTrunc (gcd a b)

## From a given start node, step once through the list of directions,
## returning the node reached and the list of indices where an "end node" was passed.
##
## This function allows us to interpret the input as a graph where
## each node has exactly one out-edge and the edges are labelled by these index lists.
stepDirections : Input, Node -> (Node, List Nat)
stepDirections = \{ nodes, directions }, start ->
    (dst, ends) = List.walkWithIndex directions (start, []) \(node, endsFound), dir, i ->

        newEnds =
            if isEndNode node then
                dbg
                    "end! \(node)"

                List.append endsFound i
            else
                endsFound
        newNode =
            nodes
            |> Dict.get node
            |> orCrash
            |> followDirection dir
        (newNode, newEnds)

    (dst, ends)

endIndicesFromPath : List (List Nat), Nat -> List I64
endIndicesFromPath = \path, stepSize ->
    out, ends, stepNum <- List.walkWithIndex path []
    List.concat out (List.map ends \i -> i + stepNum * stepSize |> Num.toI64)

CycleDescriptor : { preCyclePath : List (List Nat), cyclePath : List (List Nat) }

chaseCycles : List Node, Input -> List CycleDescriptor
chaseCycles = \startNodes, inp ->
    destinies = computeDestinies (Dict.empty {}) inp (Set.fromList startNodes)
    startNodes
    |> List.map \start ->
        (cycleNode, preCyclePath) =
            destinies
            |> Dict.get start
            |> orCrash
        (cycleNode2, cyclePath) =
            destinies
            |> Dict.get cycleNode
            |> orCrash
        expect cycleNode == cycleNode2
        { preCyclePath, cyclePath }

NextNodeCache edgeLabel : Dict Node (Node, List edgeLabel)

## Compute the destinies of every node reachable from `todo`, updating `cache`.
##
## Maintains a cache mapping nodes to their "destinies":
## Since all nodes are destined to eventually end up in a cycle,
## we define the "destiny" of a node as a pair of
## - Its "destination" -- the first node in its cycle reachable from it
## - The path of edges to its destination
##
## The destiny of a node which is a member of a cycle is itself.
## Therefore, the cache has a maximum cycle length of 1.
computeDestinies : NextNodeCache (List Nat), Input, Set Node -> NextNodeCache (List Nat)
computeDestinies = \cache, inp, todo ->
    when setArbitrary todo is
        Err Empty -> cache
        Ok start ->
            updates = chaseCycle start (cachedNextFrom cache inp)
            newCache =
                cache
                |> Dict.insertAll updates
            newTodo =
                todo
                |> setRemoveAllDict updates
            computeDestinies newCache inp newTodo

cachedNextFrom : NextNodeCache (List Nat), Input -> (Node -> (Node, List (List Nat)))
cachedNextFrom = \cache, inp ->
    \node ->
        when Dict.get cache node is
            Ok outcome -> outcome
            Err KeyNotFound ->
                (nextNode, edgeLabel) = stepDirections inp node
                (nextNode, [edgeLabel])

## Walks from `start` until encountering a cycle,
## returning a cache with the destinies of all intermediate nodes.
##
## The returned cache is acyclic with one exception:
## The first node encountered in the cycle points back to itself.
chaseCycle : Node, (Node -> (Node, List edgeLabel)) -> NextNodeCache edgeLabel
chaseCycle = \start, nextFrom ->
    chaseCycleTR start nextFrom (Dict.empty {}) []
chaseCycleTR = \node, nextFrom, seen, pathSoFar ->
    nodeBk = node |> Str.concat "bk" # Work around miscompilation.. Roc is immature

    when Dict.get seen node is
        Ok cycleStart ->
            # `node` is the first node in the cycle which is reachable from `start`.
            # All the intermediate nodes (recorded in `seen`) are destined to end up at `node`.
            seen
            |> Dict.map \_seenNode, i ->
                pathFromSeenToNode =
                    if i < cycleStart then
                        List.sublist pathSoFar { start: i, len: cycleStart - i }
                    else
                        List.dropFirst pathSoFar i

                (node, pathFromSeenToNode)

        Err KeyNotFound ->
            (nextNode, nextPath) = nextFrom node

            nodeRestore = nodeBk |> Str.replaceLast "bk" ""
            # `nodeRestore` should equal `node` but `node` somehow changes value due to a miscompilation
            chaseCycleTR nextNode nextFrom (Dict.insert seen nodeRestore (List.len pathSoFar)) (List.concat pathSoFar nextPath)

alignCycles : List CycleDescriptor -> List CycleDescriptor
alignCycles = \cycleDescrs ->
    max =
        cycleDescrs
        |> List.map \{ preCyclePath } -> List.len preCyclePath
        |> List.max
    when max is
        Ok desiredStart ->
            cycleDescrs
            |> List.map \descr -> advanceCycle descr desiredStart
        Err _ -> []


## Returns a new cycle descriptor with `preCyclePath` extended to length `desiredStart`.
advanceCycle : CycleDescriptor, Nat -> CycleDescriptor
advanceCycle = \{ preCyclePath, cyclePath }, desiredStart ->
    growth = desiredStart - List.len preCyclePath
    cycleLen = List.len cyclePath
    cycleCopies = Num.divTrunc growth cycleLen
    cycleRotation = growth % cycleLen
    cyclePrefix = List.takeFirst cyclePath cycleRotation

    {
        preCyclePath: preCyclePath
        |> List.concat (List.join (List.repeat cyclePath cycleCopies))
        |> List.concat cyclePrefix,
        cyclePath: cyclePath
        |> List.dropFirst cycleRotation
        |> List.concat cyclePrefix,
    }

part2 : Input -> Nat
part2 = \{ directions, nodes } ->
    startNodes =
        nodes
        |> Dict.keys
        |> List.keepIf \k -> isStartNode k

    cycleDescrs =
        chaseCycles startNodes { directions, nodes }
        |> alignCycles
    cycleStart =
        cycleDescrs
        |> List.get 0
        |> orCrash
        |> .preCyclePath
        |> List.len

    directionsLen = List.len directions

    preCycleWins =
        cycleDescrs
        |> List.map \{ preCyclePath } -> endIndicesFromPath preCyclePath directionsLen
        |> listReduce intersectionSorted
        |> orCrash
    when preCycleWins is
        [win, ..] -> Num.toNat win
        [] ->
            congruenceSets =
                cycleDescrs
                |> List.map \{ cyclePath } ->
                    endIndices =
                        cyclePath
                        |> endIndicesFromPath directionsLen
                        |> Set.fromList
                    cycleLen = List.len cyclePath * directionsLen
                    (endIndices, Num.toI64 cycleLen)

            dbg
                congruenceSets

            congruenceSets
            |> List.walk (Set.single 0, 1) mergeCongruenceSets
            |> .0
            |> Set.toList
            |> List.min
            |> orCrash
            |> Num.toNat
            |> Num.add (cycleStart * directionsLen)

# Additional tests

example4 =
    """
    LR

    22B = (22C, 22C)
    22C = (22Z, 22Z)
    22Z = (22B, 22B)
    33A = (33B, XXX)
    33B = (XXX, 33C)
    33C = (22B, XXX)
    XXX = (XXX, XXX)
    """

expect
    answer = part2 (parse example4)
    answer == 5

example5 =
    """
    L

    11A = (11B, XXX)
    11B = (11C, XXX)
    11C = (11Z, XXX)
    11Z = (11D, XXX)
    11D = (12Z, XXX)
    12Z = (11D, XXX)
    22A = (22Z, XXX)
    22Z = (22B, XXX)
    22B = (22Z, XXX)
    XXX = (XXX, XXX)
    """

expect
    answer = part2 (parse example5)
    answer == 3

example6 =
    """
    L

    11A = (11B, XXX)
    11B = (11C, XXX)
    11C = (11Z, XXX)
    11Z = (11D, XXX)
    11D = (12Z, XXX)
    12Z = (11Z, XXX)
    22A = (22B, XXX)
    22B = (22Z, XXX)
    22Z = (22A, XXX)
    33A = (33B, XXX)
    33B = (33C, XXX)
    33C = (33D, XXX)
    33D = (33E, XXX)
    33E = (33Z, XXX)
    33Z = (33F, XXX)
    33F = (3GZ, XXX)
    3GZ = (33H, XXX)
    33H = (33D, XXX)
    XXX = (XXX, XXX)
    """

expect
    answer = part2 (parse example6)
    answer == 5

# Helper functions

## Compute the intersection of two sets represented as sorted lists in linear time
intersectionSorted : List I64, List I64 -> List I64
intersectionSorted = \xs, ys ->
    intersectionSortedTR xs ys []
intersectionSortedTR = \xs, ys, acc ->
    when (xs, ys) is
        ([], _) | (_, []) -> acc
        ([x, .. as xs2], [y, .. as ys2]) ->
            when Num.compare x y is
                EQ -> intersectionSortedTR xs2 ys2 (List.append acc x)
                LT -> intersectionSortedTR xs2 ys acc
                GT -> intersectionSortedTR xs ys2 acc

        _ -> crash "unreachable"

## Apply a partial map to the Cartesian product of two sets
filterMapPairs : Set a, Set a, (a, a -> Result b *) -> Set b
filterMapPairs = \xs, ys, f ->
    x <- Set.joinMap xs
    y <- Set.joinMap ys
    when f x y is
        Ok v -> Set.single v
        Err _ -> Set.empty {}

## Unwrap a `Result`, crashing in the error case
orCrash : Result v e -> v where e implements Inspect
orCrash = \r ->
    when r is
        Ok v -> v
        Err e ->
            dbg
                e

            crash "orCrash encounted Err"

## Returns an arbitrary element from a set in constant time
setArbitrary = \set ->
    Set.walkUntil set (Err Empty) \_, elem -> Break (Ok elem)

## Removes all the keys in a dict from a set
setRemoveAllDict = \set, dict ->
    Dict.walk dict set \acc, k, _ -> Set.remove acc k

listReduce : List elem, (elem, elem -> elem) -> Result elem [Empty]
listReduce = \list, combine ->
    when list is
        [first, .. as rest] -> Ok (List.walk rest first combine)
        [] -> Err Empty