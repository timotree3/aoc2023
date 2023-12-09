app "day6"
    packages { pf: "https://github.com/roc-lang/basic-cli/releases/download/0.7.0/bkGby8jb0tmZYsy2hg1E_B2QrCgcSTxdUlHtETwm5m4.tar.br" }
    imports [pf.Stdout, pf.Task.{ Task }, "../inputs/day6.txt" as input : Str]
    provides [main] to pf

Input : List Record
Record : { time : U64, distance : U64 }

parseTwoLines : Str -> (Str, Str)
parseTwoLines = \inp ->
    lines =
        inp
        |> Str.trim
        |> Str.split "\n"

    when lines is
        [line1, line2] ->
            (line1, line2)

        _ -> crash "expected exactly two lines in input"

parse1 : Str -> Input
parse1 = \inp ->
    (times, distances) = parseTwoLines inp
    List.map2 (parseLinePt1 times) (parseLinePt1 distances) \time, distance -> { time, distance }

parseLinePt1 = \line ->
    line
    |> Str.split " "
    |> List.keepOks Str.toU64

parse2 : Str -> Input
parse2 = \inp ->
    (time, distance) = parseTwoLines inp
    [{ time: parseLinePt2 time, distance: parseLinePt2 distance }]

parseLinePt2 = \line ->
    line
    |> Str.replaceFirst "Time:" ""
    |> Str.replaceFirst "Distance:" ""
    |> Str.replaceEach " " ""
    |> Str.toU64
    |> orCrash

intervalPartitionPoint : { start : Int a, end : Int a }, (Int a -> [Left, Right]) -> Int a
intervalPartitionPoint = \{ start, end }, cmp ->
    expect
        start <= end

    if start >= end then
        start
    else
        # [2, 8)
        #      ^ end
        #  ^ start
        # midpoint = 5
        midpoint = Num.divTrunc (start + end) 2
        when cmp midpoint is
            Right ->
                # 5 belongs Right; recurse with [2, 5)
                intervalPartitionPoint { start, end: midpoint } cmp

            Left ->
                # 5 belongs Left; recurse with (5, 8)
                intervalPartitionPoint { start: midpoint + 1, end } cmp

numWaysToBeatNaive : Record -> U64
numWaysToBeatNaive = \{ time, distance: recordDistance } ->
    List.range { start: At 0, end: At time }
    |> List.map \button -> score { time, button }
    |> List.keepIf \dist -> dist > recordDistance
    |> List.len
    |> Num.toU64

score = \{ time, button } -> (time - button) * button

# Works in O(log time)
numWaysToBeat : Record -> U64
numWaysToBeat = \{ time, distance: recordDistance } ->
    leastWinningButton =
        intervalPartitionPoint { start: 0, end: Num.divTrunc time 2 + 1 } \button ->
            if score { time, button } > recordDistance then Right else Left

    # All button numbers <= time//2 are losers. Since the problem is symmetric, there are therefore no winners.
    if leastWinningButton > Num.divTrunc time 2 then
        0
    else
        expect
            score { time, button: leastWinningButton } > recordDistance

        expect
            score { time, button: leastWinningButton - 1 } <= recordDistance

        expect
            leastWinningButton <= Num.divTrunc time 2

        greatestWinningButton = time - leastWinningButton
        expect score { time, button: greatestWinningButton } > recordDistance
        expect score { time, button: greatestWinningButton + 1 } <= recordDistance

        greatestWinningButton - leastWinningButton + 1

testRecords =
    List.range { start: At 0, end: Length 10 }
    |> List.joinMap \t ->
        List.range { start: At 0, end: At (Num.divTrunc (t * t) 4) }
        |> List.map \r -> { time: t, distance: r }

expect
    testRecords
    |> List.all \record ->
        naive = numWaysToBeatNaive record
        opt = numWaysToBeat record
        expect naive == opt
        naive == opt

solve : Input -> U64
solve = \records ->
    records
    |> List.map numWaysToBeat
    |> List.product

example : Str
example =
    """
    Time:      7  15   30
    Distance:  9  40  200
    """

expect
    answer = solve (parse1 example)
    answer == 288

expect
    answer = solve (parse2 example)
    answer == 71503

main : Task {} I32
main =
    {} <- Stdout.line "Part 1: \(Num.toStr (solve (parse1 input)))" |> Task.await
    Stdout.line "Part 2: \(Num.toStr (solve (parse2 input)))"

orCrash : Result v e -> v where e implements Inspect
orCrash = \r ->
    when r is
        Ok v -> v
        Err e ->
            dbg
                e

            crash "orCrash encounted Err"
