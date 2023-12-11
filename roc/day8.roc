app "day8"
    packages { pf: "https://github.com/roc-lang/basic-cli/releases/download/0.7.0/bkGby8jb0tmZYsy2hg1E_B2QrCgcSTxdUlHtETwm5m4.tar.br" }
    imports [pf.Stdout, pf.Task.{ Task }, "../inputs/day8.txt" as input : Str]
    provides [main] to pf

Input : { directions : List [Left, Right], nodes : Dict Str (Str, Str) }

parse : Str -> Input
parse = \inp ->
    { before: directions, after: nodes } = inp |> Str.trim |> Str.splitFirst "\n\n" |> orCrash

    { directions: parseDirections directions, nodes: parseNodes nodes }

parseDirections : Str -> List [Left, Right]
parseDirections = \s ->
    s
    |> Str.toUtf8
    |> List.map parseDirection

parseDirection = \b ->
    when b is
        'L' -> Left
        'R' -> Right
        _ -> crash "expected direction to be 'L' or 'R'"

parseNodes : Str -> Dict Str (Str, Str)
parseNodes = \s ->
    s
    |> Str.split "\n"
    |> List.map parseNode
    |> Dict.fromList

parseNode : Str -> (Str, (Str, Str))
parseNode = \line ->
    { before: node, after: exits } = Str.splitFirst line " = (" |> orCrash
    { before: left, after: right } =
        exits
        |> Str.replaceEach ")" ""
        |> Str.splitFirst ", "
        |> orCrash
    (node, (left, right))

startNode = "AAA"
endNode = "ZZZ"

followDirection = \(left, right), direction ->
    when direction is
        Left -> left
        Right -> right

step = \node, directions, nodes, i ->
    dir = List.get directions (Num.rem i (List.len directions)) |> orCrash

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

part1 : Input -> Nat
part1 = \{ directions, nodes } ->
    walk startNode directions nodes 0

isStartNode = \name -> Str.endsWith name "A"
isEndNode = \name -> Str.endsWith name "Z"

intersectionSorted = \xs, ys ->
    intersectionSortedTC xs ys []
intersectionSortedTC = \xs, ys, acc ->
    when (xs, ys) is
        ([], _) | (_, []) -> acc
        ([x, .. as xs2], [y, .. as ys2]) ->
            when Num.compare x y is
                EQ -> intersectionSortedTC xs2 ys2 (List.append acc x)
                LT -> intersectionSortedTC xs2 ys acc
                GT -> intersectionSortedTC xs ys2 acc

        _ -> crash "unreachable"

xgcd : I64, I64 -> (I64, I64, I64)
xgcd = \a, b ->
    (r, s, t) = xgcdTC (Num.max a b) (Num.min a b) 1 0 0 1
    if a >= b then
        (r, s, t)
    else
        (r, t, s)

xgcdTC = \r0, r1, s0, s1, t0, t1 ->
    if r1 == 0 then
        (r0, s0, t0)
    else
        q2 = Num.divTrunc r0 r1
        r2 = r0 % r1
        s2 = s0 - (q2 * s1)
        t2 = t0 - (q2 * t1)
        xgcdTC r1 r2 s1 s2 t1 t2

expect
    answer = xgcd 240 46
    answer == (2, -9, 47)

expect
    answer = xgcd 46 240
    answer == (2, 47, -9)

filterMapPairs : Set a, Set a, (a, a -> Result b *) -> Set b
filterMapPairs = \xs, ys, f ->
    x <- Set.joinMap xs
    y <- Set.joinMap ys
    when f x y is
        Ok v -> Set.single v
        Err _ -> Set.empty {}

mergeCongruenceSets : (Set I64, I64), (Set I64, I64) -> (Set I64, I64)
mergeCongruenceSets = \(ms, p), (ns, q) ->
    (filterMapPairs ms ns \m, n -> congruentToBoth m p n q, lcm p q)

## Returns the the lowest k such that k % p == m and k % q == n.
# e.q for k % 3 == 2 and k % 5 == 3
# solution: start with n = 2. This satisfies n % 3 = 2.
# Now the question is how many 3s to we have to add to get n % 5 == 3
# Right now n % 5 == 2. We have to add 1 mod 5. 1/3 mod 5 = 2. Therefore we have to add 2 * 3.
# n = 2 + 2 * 3 = 8
#
# General algorithm for finding n st n % p == m and n % q == k:
# n = m + p * ((k - m)/p mod q)
# Specific instance:
# 8 = 2 + 3 * ((3 - 2)/3 mod 5)
# 8 = 3 + 5 * ((2 - 3)/5 mod 3)
#
# Now let's say p = 6 and q = 9
# e.g. n st n % 6 == 4 and n % 9 == 5
# Same algorithm?
# n = 4 + 6 * ((5 - 4)/6 mod 9) -- doesn't exist
# Let's try n st n % 6 == 4 and n % 9 == 7
# n = 4 + 6 * ((7 - 4)/6 mod 9) = 4 + 6 * 2 = 16
#
# Is 16 unique mod 18? Obviously..
# Is p * (n/p mod q) mod lcm(p, q) unique?
# We know that (n/p mod q) has unique answers mod (q/gcd(p, q))
# Therefore we know that p * (n/p mod q) has unique answers mod (p * q / gcd(p,q)) = lcm(p, q)
congruentToBoth = \m, p, n, q ->
    dbg
        { m, p, n, q }

    x <- divMod (n - m) p q |> Result.map
    m + p * x

expect congruentToBoth 2 3 3 5 == Ok 8
expect congruentToBoth 4 6 7 9 == Ok 16
expect congruentToBoth 0 2 1 6 == Err InvalidDivision

# Euclidean mod
modE = \m, n ->
    r = m % n
    if r < 0 then
        r + n
    else
        r

divMod = \m, n, p ->
    mp = m |> modE p
    np = n |> modE p
    (r, _s, t) = xgcd p np
    tpos = if t < 0 then t + p else t
    zeroDivN = Num.divTrunc p r
    expect (np * zeroDivN) % p == 0
    if mp % r == 0 then
        answer = ((Num.divTrunc mp r) * tpos) % zeroDivN
        expect (answer * n) % p == mp
        Ok answer
    else
        dbg
            "\(Num.toStr mp) / \(Num.toStr np) mod \(Num.toStr p) doesn't exist"

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

stepDirections : Input, Str -> (Str, List Nat)
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

chaseCycle : Dict Str (Str, List (List Nat)), Input, Str -> Dict Str (Str, List (List Nat))
chaseCycle = \outcomes, inp, start ->
    chaseCycleTC : Str, Dict Str Nat, List (List Nat) -> Dict Str (Str, List (List Nat))
    chaseCycleTC = \node, seen, ends ->
        nodeBk = node |> Str.concat "bk" # Work around miscompilation

        when Dict.get seen node is
            Ok cycleStart ->
                seen
                |> Dict.map \_, i ->
                    newEnds =
                        if i < cycleStart then
                            List.sublist ends { start: i, len: cycleStart - i }
                        else
                            List.dropFirst ends i

                    (node, newEnds)

            Err KeyNotFound ->
                (dst, nodeEnds) =
                    when Dict.get outcomes node is
                        Ok p -> p
                        Err KeyNotFound ->
                            p = stepDirections inp node
                            (p.0, [p.1])

                nodeRestore = nodeBk |> Str.replaceFirst "bk" ""
                chaseCycleTC dst (Dict.insert seen nodeRestore (List.len ends)) (List.concat ends nodeEnds)
    chaseCycleTC start (Dict.empty {}) []

dictArbitrary = \dict ->
    Dict.walkUntil dict (Err Empty) \_, k, v -> Break (Ok (k, v))

# Concatenates cyclic edges so that the maximum cycle length is 1
chaseCycles : Dict Str (Str, List (List Nat)), Input, Dict Str (Str, List (List Nat)) -> Dict Str (Str, List (List Nat))
chaseCycles = \outcomes, inp, todo ->
    when dictArbitrary todo is
        Err Empty -> outcomes
        Ok (start, _) ->
            updates = chaseCycle outcomes inp start
            newOutcomes =
                outcomes
                |> Dict.insertAll updates
            newTodo =
                todo
                |> Dict.removeAll updates
            chaseCycles newOutcomes inp newTodo

advanceCycle = \{ preCycleEnds, cycleEnds }, desiredLen ->
    growth = desiredLen - List.len preCycleEnds
    cycleLen = List.len cycleEnds
    cycleCopies = Num.divTrunc growth cycleLen
    cycleRotation = growth % cycleLen
    cyclePrefix = List.takeFirst cycleEnds cycleRotation

    {
        preCycleEnds: preCycleEnds
        |> List.concat (List.join (List.repeat cycleEnds cycleCopies))
        |> List.concat cyclePrefix,
        cycleEnds: cycleEnds
        |> List.dropFirst cycleRotation
        |> List.concat cyclePrefix,
    }

flattenEnds = \endsPerStep, stepSize ->
    out, ends, stepNum <- List.walkWithIndex endsPerStep []
    List.concat out (List.map ends \i -> i + stepNum * stepSize |> Num.toI64)

part2 : Input -> Nat
part2 = \{ directions, nodes } ->
    startNodes =
        nodes
        |> Dict.keepIf \(k, _) -> isStartNode k
        |> Dict.map \_, _ -> ("", [])

    outcomes = chaseCycles (Dict.empty {}) { directions, nodes } startNodes
    dbg
        outcomes

    cycleDescrs =
        startNodes
        |> Dict.keys
        |> List.map \start ->
            (cycleNode, preCycleEnds) =
                outcomes
                |> Dict.get start
                |> orCrash
            (cycleNode2, cycleEnds) =
                outcomes
                |> Dict.get cycleNode
                |> orCrash
            expect cycleNode == cycleNode2
            { preCycleEnds, cycleEnds }

    dbg
        cycleDescrs

    uniformPreLen =
        cycleDescrs
        |> List.map \{ preCycleEnds } -> List.len preCycleEnds
        |> List.max
        |> orCrash

    uniformCycleDescrs =
        cycleDescrs
        |> List.map \descr -> advanceCycle descr uniformPreLen

    dbg
        uniformCycleDescrs

    directionsLen = List.len directions

    preCycleWins =
        uniformCycleDescrs
        |> List.map \{ preCycleEnds } -> flattenEnds preCycleEnds directionsLen
        |> List.walk (Err Empty) \state, b ->
            when state is
                Err Empty -> Ok b
                Ok a -> Ok (intersectionSorted a b)
        |> orCrash
    when List.get preCycleWins 0 is
        Ok win -> Num.toNat win
        Err OutOfBounds ->
            flattened =
                uniformCycleDescrs
                |> List.map \{ cycleEnds } ->
                    endsSet =
                        cycleEnds
                        |> flattenEnds directionsLen
                        |> Set.fromList
                    cycleLen = List.len cycleEnds * directionsLen
                    (endsSet, Num.toI64 cycleLen)

            dbg
                flattened

            flattened
            |> List.walk (Set.single 0, 1) mergeCongruenceSets
            |> .0
            |> Set.toList
            |> List.min
            |> orCrash
            |> Num.toNat
            |> Num.add (uniformPreLen * directionsLen)

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

example2 =
    """
    LLR

    AAA = (BBB, BBB)
    BBB = (AAA, ZZZ)
    ZZZ = (ZZZ, ZZZ)
    """

expect
    answer = part1 (parse example1)
    answer == 2

expect
    answer = part1 (parse example2)
    answer == 6

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
    answer == 6

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

main : Task {} I32
main =
    {} <- Stdout.line "Part 1: \(Num.toStr (part1 (parse input)))" |> Task.await
    Stdout.line "Part 2: \(Num.toStr (part2 (parse input)))"

orCrash : Result v e -> v where e implements Inspect
orCrash = \r ->
    when r is
        Ok v -> v
        Err e ->
            dbg
                e

            crash "orCrash encounted Err"
