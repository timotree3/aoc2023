app "dayxx"
    packages { pf: "https://github.com/roc-lang/basic-cli/releases/download/0.8.1/x8URkvfyi9I0QhmVG98roKBUs_AZRkLFwFJVJ3942YA.tar.br" }
    imports [pf.Stdout, pf.Task.{ Task }, "../inputs/dayxx.txt" as input : Str]
    provides [main] to pf

Input : List Foo

parse : Str -> Input
parse = \inp ->
    inp
    |> Str.trim
    |> Str.split "\n"
    |> List.map parseLine

parseLine = \line ->
    line
    |> Str.split " "
    |> crash "todo"

part1 : Input -> U64
part1 = \x ->
    crash "todo"

part2 : Input -> U64
part2 = \x ->
    crash "todo"

example : Str
example =
    """
    """

expect
    answer = part1 (parse example)
    answer == crash "val"

# expect
#     answer = part2 (parse example)
#     answer == ??

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
