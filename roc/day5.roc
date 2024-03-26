app "day5"
    packages { pf: "https://github.com/roc-lang/basic-cli/releases/download/0.8.1/x8URkvfyi9I0QhmVG98roKBUs_AZRkLFwFJVJ3942YA.tar.br" }
    imports [pf.Stdout, pf.Task.{ Task }, "../inputs/day5.txt" as input : Str]
    provides [main] to pf

Input : {
    seeds : List U64,
    maps : List (List MapRange),
}

Range a : { start : U64, end : U64 }a

MapRange : Range {
    dstOffset : I64,
}

parse : Str -> Input
parse = \inp ->
    sections = inp |> Str.trim |> Str.split "\n\n"
    when sections is
        [seedsLine, .. as mapSections] ->
            { seeds: parseSeeds seedsLine, maps: List.map mapSections parseMap }

        _ -> crash "expected at least two sections in input"

parseSeeds = \line ->
    line
    |> Str.replaceFirst "seeds: " ""
    |> Str.split " "
    |> List.mapTry Str.toU64
    |> orCrash

parseMap = \mapSection ->
    { after } = Str.splitFirst mapSection " map:\n" |> orCrash
    after
    |> Str.split "\n"
    |> List.map parseMapRange

parseMapRange : Str -> MapRange
parseMapRange = \line ->
    numerals =
        line
        |> Str.split " "
        |> List.mapTry Str.toU64
        |> orCrash
    when numerals is
        [dstStart, srcStart, len] ->
            { start: srcStart, end: srcStart + len, dstOffset: Num.toI64 dstStart - Num.toI64 srcStart }

        _ -> crash "expected 3 numerals describing range of mapped values"

cmpNum = \a, b ->
    if a < b then
        LT
    else if b < a then
        GT
    else
        EQ

sortByKey : List elem, (elem -> Num *) -> List elem
sortByKey = \l, key -> List.sortWith l \a, b -> cmpNum (key a) (key b)

# Binary search with custom comparison function
#
# Assuming `xs` is sorted according to `cmp`, `binarySearchWith xs cmp`
# returns an index `i` such that
# - For all `j` less than `i`, `cmp xs[j] == LT`
# - For all `j` greater than or equal to `i`, `cmp xs[j] == GE`
#
# In the special case where `cmp = \elem -> if elem < x then LT else GE`, we have
# `xs[i - 1] < x && x <= xs[i]`
binarySearchWith : List a, (a -> [LT, GE]) -> U64
binarySearchWith = \list, cmp ->
    go = \sublist, offset ->
        len = List.len sublist
        midpoint = Num.divTrunc len 2
        when List.get sublist midpoint is
            Ok elem ->
                when cmp elem is
                    LT ->
                        # [0, 1, 2, 3]
                        #        ^ midpoint
                        # 2 < needle
                        go (List.dropFirst sublist (midpoint + 1)) (offset + midpoint + 1)

                    GE ->
                        # [0, 1, 2, 3]
                        #        ^ midpoint
                        # needle <= 2
                        go (List.takeFirst sublist midpoint) offset

            Err OutOfBounds -> # Base case: List is empty. Return accumulator
                offset
    i = go list 0
    expect binarySearchPostcondition list i cmp
    i

okImplies = \result, pred ->
    when result is
        Ok x -> pred x
        Err _ -> Bool.true

binarySearchPostcondition = \xs, i, cmp ->
    left = List.get xs (Num.subWrap i 1) |> okImplies (\x -> cmp x == LT)
    right = List.get xs i |> okImplies \x -> cmp x == GE
    left && right

binarySearchByKey : List a, Num b, (a -> Num b) -> U64
binarySearchByKey = \list, val, key ->
    binarySearchWith list \elem -> if key elem < val then LT else GE

takeWhile : List elem, (elem -> Bool) -> List elem
takeWhile = \l, pred ->
    when List.findFirstIndex l (\elem -> !(pred elem)) is
        Ok i -> List.takeFirst l i
        Err NotFound -> l

rangeIntersects = \a, b -> rangeIntersection a b |> rangeEmpty |> Bool.not

# If `map` is a list of disjoint ranges sorted by `.start`,
# `keepIfIntersects map r == List.keepIf map \m -> m |> rangeIntersects r`
#
# Time complexity: O(log n + length of output)
keepIfIntersects : List (Range a), Range * -> List (Range a)
keepIfIntersects = \map, r ->
    idx = binarySearchByKey map (r.start + 1) .start
    map
    |> List.dropFirst (Num.subSaturated idx 1)
    |> takeWhile (\m -> m |> rangeIntersects r)

rangeIntersection = \a, b ->
    { start: Num.max a.start b.start, end: Num.min a.end b.end }

rangeEmpty = \{ start, end } -> end <= start

addI64 = \a, b ->
    a |> Num.toI64 |> Num.add b |> Num.toU64

rangeOffset = \{ start, end }, offset ->
    { start: start |> addI64 offset, end: end |> addI64 offset }

walkMap : List a, state, (state, a -> (b, state)) -> (List b, state)
walkMap = \l, state, f ->
    List.walk l ([], state) \(mappedSoFar, oldState), elem ->
        (mapped, newState) = f oldState elem
        (List.append mappedSoFar mapped, newState)

mapWindows2 : List a, (a -> b), (a, a -> b), (a -> b) -> List b
mapWindows2 = \list, mapFirst, mapPair, mapLast ->
    when list is
        [] -> []
        [first, .. as rest] ->
            (pairs, last) =
                list
                |> walkMap first \prev, current -> ((prev, current), current)
            pairs
            |> List.map \(a, b) -> mapPair a b
            |> List.prepend (mapFirst first)
            |> List.append (mapLast last)

rangeGaps : List (Range *) -> List (Range {})
rangeGaps = \l ->
    when l is
        [] -> [{ start: 0, end: Num.maxU64 }]
        _ ->
            mapWindows2
                l
                \first -> { start: 0, end: first.start }
                \a, b -> { start: a.end, end: b.start }
                \last -> { start: last.end, end: Num.maxU64 }

applyMap = \range, map ->
    intersecting =
        map
        |> keepIfIntersects range
    skippedRanges =
        intersecting
        |> rangeGaps
        |> List.map \gap -> gap |> rangeIntersection range
    intersecting
    |> List.map \r -> r |> rangeIntersection range |> rangeOffset r.dstOffset
    |> List.concat skippedRanges
    |> List.dropIf rangeEmpty

applyMapToRanges = \ranges, map ->
    List.joinMap ranges \r -> applyMap r map

rangeSingleton = \elem -> { start: elem, end: elem + 1 }

solve = \{ seedRanges, maps } ->
    sortedMaps = List.map maps \ranges -> sortByKey ranges .start
    locationRanges =
        List.walk sortedMaps seedRanges applyMapToRanges
    locationRanges
    |> List.map .start
    |> List.min
    |> orCrash

part1 : Input -> U64
part1 = \{ seeds, maps } ->
    solve { maps, seedRanges: seeds |> List.map rangeSingleton }

pairChunks = \l ->
    l
    |> List.chunksOf 2
    |> List.mapTry \sublist ->
        when sublist is
            [a, b] -> Ok (a, b)
            _ -> Err Odd

part2 : Input -> U64
part2 = \{ seeds, maps } ->
    seedRanges = seeds |> pairChunks |> orCrash |> List.map \(start, len) -> { start, end: start + len }
    solve { maps, seedRanges }

example : Str
example =
    """
    seeds: 79 14 55 13

    seed-to-soil map:
    50 98 2
    52 50 48

    soil-to-fertilizer map:
    0 15 37
    37 52 2
    39 0 15

    fertilizer-to-water map:
    49 53 8
    0 11 42
    42 0 7
    57 7 4

    water-to-light map:
    88 18 7
    18 25 70

    light-to-temperature map:
    45 77 23
    81 45 19
    68 64 13

    temperature-to-humidity map:
    0 69 1
    1 0 69

    humidity-to-location map:
    60 56 37
    56 93 4
    """

expect
    answer = part1 (parse example)
    answer == 35

expect
    answer = part2 (parse example)
    answer == 46

main : Task {} I32
main =
    inp = parse input
    {} <- Stdout.line "Part 1: \(Num.toStr (part1 inp))" |> Task.await
    Stdout.line "Part 2: \(Num.toStr (part2 inp))"

orCrash : Result v e -> v where e implements Inspect
orCrash = \r ->
    when r is
        Ok v -> v
        Err e ->
            dbg
                e

            crash "orCrash encounted Err"
