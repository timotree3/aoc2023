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

numWaysToBeat : Record -> U64
numWaysToBeat = \{ time, distance: recordDistance } ->
    List.range { start: At 0, end: At time }
    |> List.map \buttonDuration -> (time - buttonDuration) * buttonDuration
    |> List.keepIf \dist -> dist > recordDistance
    |> List.len
    |> Num.toU64

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
