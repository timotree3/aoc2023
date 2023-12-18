app "day12"
    packages { pf: "https://github.com/roc-lang/basic-cli/releases/download/0.7.0/bkGby8jb0tmZYsy2hg1E_B2QrCgcSTxdUlHtETwm5m4.tar.br" }
    imports [pf.Stdout, pf.Task.{ Task }, "../inputs/day12.txt" as input : Str]
    provides [main] to pf

Input : List Record
Record : { pattern : List Spring, runs : List Run }
Spring : [Damaged, Operational, Unknown]
Run : Nat

parse : Str -> Input
parse = \inp ->
    inp
    |> Str.trim
    |> Str.split "\n"
    |> List.map parseLine

parseLine = \line ->
    { before, after } =
        line
        |> Str.splitFirst " "
        |> orCrash
    { pattern: parsePattern before, runs: parseRuns after }

parsePattern = \pat ->
    Str.toUtf8 pat
    |> List.map parseSpring

parseSpring = \b ->
    when b is
        '#' -> Damaged
        '.' -> Operational
        '?' -> Unknown
        _ -> crash "unexpected character in spring"

parseRuns = \runs ->
    runs
    |> Str.split ","
    |> List.mapTry Str.toNat
    |> orCrash

# printPat = \pat ->
#     pat
#     |> List.map \x ->
#         when x is
#             Unknown -> "?"
#             Damaged -> "#"
#             Operational -> "."
#     |> Str.joinWith ""

# printRuns = \runs ->
#     runs
#     |> List.map Num.toStr
#     |> Str.joinWith ","

# findSolns : Record, List [Damaged, Operational] -> List (List [Damaged, Operational])
# findSolns = \{ pattern, runs }, partialSolution ->
#     # msg1 = "findSolns \(printPat pattern) \(printRuns runs) = ?"
#     # dbg
#     #     msg1

#     ret =
#         when pattern is
#             [] ->
#                 if List.isEmpty runs then
#                     [partialSolution]
#                 else
#                     []

#             [_, .. as nextSprings] ->
#                 afterOperational =
#                     if couldStartWithOperational pattern then
#                         findSolns { pattern: nextSprings, runs } (List.append partialSolution Operational)
#                     else
#                         []
#                 afterDamage =
#                     when runs is
#                         [] -> []
#                         [firstRun, .. as nextRuns] ->
#                             if couldStartWithNDamaged pattern firstRun then
#                                 damaged =
#                                     List.repeat Damaged firstRun
#                                     |> List.append Operational
#                                     |> List.takeFirst (List.len pattern)
#                                 findSolns { pattern: List.dropFirst nextSprings firstRun, runs: nextRuns } (List.concat partialSolution damaged)
#                             else
#                                 []
#                 List.concat afterOperational afterDamage

#     msg = "findSolns \(printPat pattern) \(printRuns runs) = \(Num.toStr (List.len ret))"
#     # dbg
#     #     msg

#     ret

# couldStartWithOperational = \pattern ->
#     when pattern is
#         [Operational, ..] | [Unknown, ..] -> Bool.true
#         [] | [Damaged, ..] -> Bool.false

# couldStartWithNDamaged : List Spring, Nat -> Bool
# couldStartWithNDamaged = \pattern, n ->
#     when pattern is
#         [] | [Operational, ..] | [Unknown, ..] if n == 0 -> Bool.true
#         [Damaged, ..] if n == 0 -> Bool.false
#         [] | [Operational, ..] -> Bool.false
#         [Damaged, .. as rest] | [Unknown, .. as rest] -> couldStartWithNDamaged rest (n - 1)
#         _ -> crash "unreachable"

# checkSolution = \solution, { pattern, runs } ->
#     # dbg
#     #     solution

#     # dbg
#     #     pattern

#     matchesPat =
#         List.len solution
#         == List.len pattern
#         &&
#         List.map2 solution pattern Pair
#         |> List.all \pair ->
#             when pair is
#                 Pair Damaged Damaged | Pair Operational Operational | Pair _ Unknown -> Bool.true
#                 _ -> Bool.false
#     solnRuns =
#         groupEq solution
#         |> List.keepIf \springs -> List.all springs \s -> s == Damaged
#         |> List.map List.len
#     expect matchesPat && solnRuns == runs
#     matchesPat && solnRuns == runs

part1 : Input -> Nat
part1 = \records ->
    records
    |> List.map \{ pattern, runs } ->
        blobs = extractZones pattern
        dbg
            blobs

        placeRunsInZones runs blobs
    |> List.sum
# |> List.map \record ->
#     solns = findSolns record []
#     allValid = List.all solns \solution -> checkSolution solution record
#     expect allValid
#     expect Set.len (Set.fromList solns) == List.len solns
#     List.len solns
# |> List.sum

## A contiguous pattern of `Unknown` and `Damaged`
Zone : List ZoneSegment
ZoneSegment : { numDamagedAfter : Nat, numUnknowns : Nat }

countWhile : List elem, (elem -> Bool) -> Nat
countWhile = \list, pred ->
    list
    |> List.findFirstIndex (\elem -> !(pred elem))
    |> Result.withDefault (List.len list)

extractZones : List Spring -> List Zone
extractZones = \pattern -> extractZonesHelper pattern []

extractZonesHelper = \pattern, blobsSoFar ->
    numOperationalBefore = countWhile pattern \s -> s == Operational
    afterOperational = List.dropFirst pattern numOperationalBefore
    { zoneSegment, after } = extractZoneSegmentHelper afterOperational []
    if List.isEmpty zoneSegment then
        blobsSoFar
    else
        extractZonesHelper after (List.append blobsSoFar zoneSegment)

extractZoneSegmentHelper = \pattern, blobsSoFar ->
    numUnknowns = countWhile pattern \s -> s == Unknown
    afterUnknowns = List.dropFirst pattern numUnknowns
    numDamagedAfter = countWhile afterUnknowns \s -> s == Damaged
    afterDamage = List.dropFirst afterUnknowns numDamagedAfter
    if numUnknowns == 0 && numDamagedAfter == 0 then
        { zoneSegment: blobsSoFar, after: pattern }
    else
        extractZoneSegmentHelper afterDamage (List.append blobsSoFar { numDamagedAfter, numUnknowns })

collectSums : List (key, Num a) -> Dict key (Num a)
collectSums = \entries ->
    List.walk entries (Dict.empty {}) \dictSoFar, (key, val) ->
        Dict.update dictSoFar key \existingVal ->
            when existingVal is
                Present v -> Present (v + val)
                Missing if val == 0 -> Missing
                Missing -> Present val

step : Dict Nat Nat, List Run, Zone -> Dict Nat Nat
step = \prevResults, runs, zone ->
    results =
        prevResults
        |> Dict.toList
        |> List.joinMap \(runsEnd, numWays) ->
            runs
            |> List.dropFirst runsEnd
            |> splits
            |> List.map \{ before: runsForZone } ->
                (runsEnd + List.len runsForZone, placeRunsInZone runsForZone zone * numWays)
        |> collectSums
    dbg
        { results, zone }

    results

placeRunsInZones : List Run, List Zone -> Nat
placeRunsInZones = \runs, zones ->
    zones
    |> List.walk (Dict.single 0 1) \prevResults, zone ->
        step prevResults runs zone
    |> Dict.get (List.len runs)
    |> orCrash

placeRunsInZone : List Run, Zone -> Nat
placeRunsInZone = \runs, zone ->
    when zone is
        [] ->
            if List.isEmpty runs then
                1
            else
                0

        [segment] if List.isEmpty runs && segment.numDamagedAfter == 0 -> 1
        [segment, .. as nextSegments] ->
            runsSplits = possibleRunsSplits runs
            runsSplits
            |> List.keepIf \{ runHead } -> runHead >= segment.numDamagedAfter
            |> List.walkUntil 0 \numWaysSoFar, { before, runHead, runTail, after } ->
                # contiguousLoop = { before, numWaysSoFar, runHead, runTail, after, zoneLen: List.len zone }
                # dbg
                #     contiguousLoop

                numWaysInSegment = placeRunsInSegment before runHead segment

                if numWaysInSegment == 0 then
                    Break numWaysSoFar
                else
                    numWaysAfter =
                        when subtractBeforeZone nextSegments runTail is
                            Ok zoneAfterTail ->
                                when subtractBeforeZone zoneAfterTail 1 is
                                    Ok zoneAfterPadding -> placeRunsInZone after zoneAfterPadding
                                    Err Underflow if List.isEmpty after -> 1
                                    Err Underflow -> 0

                            Err Underflow -> 0
                    Continue (numWaysSoFar + (numWaysInSegment * numWaysAfter))

splits : List elem -> List { before : List elem, others : List elem }
splits = \list ->
    List.range { start: At 0, end: At (List.len list) }
    |> List.map \i -> List.split list i

possibleRunsSplits : List Run -> List { before : List Run, runHead : Nat, runTail : Nat, after : List Run }
possibleRunsSplits = \runs ->
    List.mapWithIndex runs \run, i ->
        { before, others } = List.split runs i
        after = List.dropFirst others 1
        List.range { start: At 1, end: At run }
        |> List.map \runHead ->
            runTail = run - runHead
            { before, runHead, runTail, after }
    |> List.join

subtractBeforeZone : Zone, Nat -> Result Zone [Underflow]
subtractBeforeZone = \zone, toSubtractAtStart ->
    if toSubtractAtStart == 0 then
        Ok zone
    else
        when zone is
            [] -> Err Underflow
            [{ numUnknowns, numDamagedAfter }, .. as nextSegments] ->
                newUnknowns = numUnknowns |> Num.subSaturated toSubtractAtStart
                toSubtractAfter = toSubtractAtStart |> Num.subSaturated numUnknowns
                newDamagedAfter = numDamagedAfter |> Num.subSaturated toSubtractAfter
                toSubtractNext = toSubtractAfter |> Num.subSaturated numDamagedAfter
                if toSubtractNext == 0 then
                    newZone = zone |> List.set 0 { numUnknowns: newUnknowns, numDamagedAfter: newDamagedAfter }
                    Ok newZone
                else
                    subtractBeforeZone nextSegments toSubtractNext

placeRunsInSegment : List Run, Run, ZoneSegment -> Nat
placeRunsInSegment = \runs, lastRun, { numUnknowns, numDamagedAfter } ->
    if numDamagedAfter == 0 then
        placeRunsInUnknowns (List.append runs lastRun) numUnknowns
    else if lastRun == numUnknowns + numDamagedAfter && runs == [] then
        placeRunsInUnknowns [] 0
    else if numDamagedAfter <= lastRun then
        restOfLastRunPlusPadding = lastRun - numDamagedAfter + 1
        if restOfLastRunPlusPadding <= numUnknowns then
            placeRunsInUnknowns runs (numUnknowns - restOfLastRunPlusPadding)
        else
            0
    else
        0

placeRunsInUnknowns = \runs, numUnknowns ->
    # e.g. runs [3, 2, 1], numUnknowns = 9
    #
    #  ###.##.#.
    #  ###.##..#
    #  ###..##.#
    #  .###.##.#
    #
    # reduce to runs [0, 0, 0] numUnknowns = 4
    #
    #  |.|.|.
    #  |.|..|
    #  |..|.|
    #  .|.|.|
    #
    # answer is (4 choose 3)
    #
    # YYYN
    # YYNY
    # YNYY
    # NYYY

    total = List.sum runs
    ret =
        if total <= numUnknowns + 1 then
            choose (numUnknowns + 1 - total) (List.len runs)
        else
            0
    # choiceResult = { runs, numUnknowns, ret }
    # dbg
    #     choiceResult

    ret

## n choose k = n!/k!(n-k)!
# https://stackoverflow.com/a/15302448/7246614
choose : Nat, Nat -> Nat
choose = \n, k ->
    if n < k then
        0
    else if k == 0 then
        1
    else
        (n * choose (n - 1) (k - 1)) // k

expect choose 4 3 == 4
expect choose 5 3 == 10
expect choose 0 0 == 1
expect choose 0 1 == 0
expect choose 1 2 == 0
expect choose 1 0 == 1
expect choose 2 1 == 2
expect choose 0 2 == 0
expect choose 50 25 == 126_410_606_437_752
expect choose 70 15 == 721_480_692_460_864

embiggen : Record -> Record
embiggen = \{ pattern, runs } -> {
    pattern: List.repeat pattern 5 |> List.intersperse [Unknown] |> List.join,
    runs: List.repeat runs 5 |> List.join,
}

printZone : Zone -> Str
printZone = \zone ->
    zone
    |> List.map \{ numUnknowns, numDamagedAfter } ->
        "?" |> Str.repeat numUnknowns |> Str.concat ("#" |> Str.repeat numDamagedAfter)
    |> Str.joinWith ""

part2 : Input -> Nat
part2 = \records ->
    records
    |> List.map embiggen
    |> List.map \{ pattern, runs } ->
        zones = extractZones pattern
        dbg
            zones |> List.map printZone |> Str.joinWith "."

        placeRunsInZones runs zones
    |> List.sum

example : Str
example =
    """
    ???.### 1,1,3
    .??..??...?##. 1,1,3
    ?#?#?#?#?#?#?#? 1,3,1,6
    ????.#...#... 4,1,1
    ????.######..#####. 1,6,5
    ?###???????? 3,2,1
    """

expect
    answer = part1 (parse example)
    answer == 21

expect
    answer = part1 (parse "??#?.???#?? 1,3")
    answer == 3

expect
    answer = part1 (parse "?###???????? 3,2,1")
    answer == 10
expect
    answer = part1 (parse ".????#??????###.? 1,1,1,1,5")
    answer == 2

expect
    answer = part1 (parse "????.######..#####. 1,6,5")
    answer == 4

expect
    answer = part1 (parse ".??..??...?##.?.??..??...?##.?.??..??...?##.?.??..??...?##.?.??..??...?##. 1,1,3,1,1,3,1,1,3,1,1,3,1,1,3")
    answer == 16384

expect
    answerManual = placeRunsInUnknowns (List.repeat [3, 3, 1] 5 |> List.join) (20 * 5 + 4)
    answer = part2 (parse "???????????????????? 3,3,1")
    answer == answerManual

expect
    answerManual = placeRunsInUnknowns (List.repeat [2, 1, 1, 1, 1] 5 |> List.join) (15 * 5 + 4)
    answer = part2 (parse "??????????????? 2,1,1,1,1")
    answer == answerManual

expect
    answer = part2 (parse example)
    answer == 525152

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

groupBy : List a, (a, a -> Bool) -> List (List a)
groupBy = \l, pred ->
    List.walk l [] \groups, elem ->
        when List.last groups |> Result.try List.last is
            Ok prev if pred prev elem ->
                List.update groups (List.len groups - 1) \group ->
                    List.append group elem

            _ -> List.append groups [elem]

groupEq = \l -> groupBy l \a, b -> a == b
