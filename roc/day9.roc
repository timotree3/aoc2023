app "day9"
    packages { pf: "https://github.com/roc-lang/basic-cli/releases/download/0.8.1/x8URkvfyi9I0QhmVG98roKBUs_AZRkLFwFJVJ3942YA.tar.br" }
    imports [pf.Stdout, pf.Task.{ Task }, "../inputs/day9.txt" as input : Str]
    provides [main] to pf

Input : List (List I64)

parse : Str -> Input
parse = \inp ->
    inp
    |> Str.trim
    |> Str.split "\n"
    |> List.map parseLine

parseLine = \line ->
    line
    |> Str.split " "
    |> List.mapTry Str.toI64
    |> orCrash

# In-place, but requires input and output are same type
# mapAdjacent : List a, (a, a -> a) -> List a
mapAdjacent = \l, f -> mapAdjacentHelper l f 0
mapAdjacentHelper = \l, f, i ->
    when List.get l (i + 1) is
        Ok y ->
            newL = List.update l i \x -> f x y
            mapAdjacentHelper newL f (i + 1)

        Err OutOfBounds ->
            List.dropLast l 1

differences = \samples ->
    mapAdjacent samples \a, b -> b - a

expect
    answer = differences [1, 2]
    answer == [1]

extrapolateForwards = \samples ->
    if List.all samples \s -> s == 0 then
        0
    else
        last = List.last samples |> orCrash
        diff = extrapolateForwards (differences samples)
        last + diff

part1 : Input -> I64
part1 = \functions ->
    functions
    |> List.map extrapolateForwards
    |> List.sum

extrapolateBackwards = \samples ->
    if List.all samples \s -> s == 0 then
        0
    else
        first = List.first samples |> orCrash
        diff = extrapolateBackwards (differences samples)
        first - diff

part2 : Input -> I64
part2 = \functions ->
    functions
    |> List.map extrapolateBackwards
    |> List.sum

example : Str
example =
    """
    0 3 6 9 12 15
    1 3 6 10 15 21
    10 13 16 21 30 45
    """

expect
    answer = part1 (parse example)
    answer == 114

expect
    answer = part2 (parse example)
    answer == 2

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
