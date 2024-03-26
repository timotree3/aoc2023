app "day13"
    packages { pf: "https://github.com/roc-lang/basic-cli/releases/download/0.8.1/x8URkvfyi9I0QhmVG98roKBUs_AZRkLFwFJVJ3942YA.tar.br" }
    imports [pf.Stdout, pf.Task.{ Task }, "../inputs/day13.txt" as input : Str]
    provides [main] to pf

Input : List Grid
Grid : List (List Tile)
Tile : [Ash, Rock]

parse : Str -> Input
parse = \inp ->
    inp
    |> Str.trim
    |> Str.split "\n\n"
    |> List.map parseGrid

parseGrid = \pat ->
    pat
    |> Str.split "\n"
    |> List.map parseLine

parseLine = \line ->
    line
    |> Str.toUtf8
    |> List.map parseTile

parseTile = \byte ->
    when byte is
        '#' -> Rock
        '.' -> Ash
        _ -> crash "unexpected tile in input"

findHorizontalReflectionWithError = \grid, desiredError ->
    List.range { start: At 1, end: Before (List.len grid) }
    |> List.findFirst \numRowsAbove -> horizontalReflectionError grid numRowsAbove == desiredError

horizontalReflectionError = \grid, numRowsAbove ->
    rowsAbove = List.takeFirst grid numRowsAbove |> List.reverse
    rowsBelow = List.dropFirst grid numRowsAbove

    List.map2 rowsAbove rowsBelow editDistance
    |> List.sum

editDistance = \xs, ys ->
    List.map2 xs ys \x, y -> if x != y then 1 else 0
    |> List.sum

findReflectionWithError = \grid, desiredError ->
    findHorizontalReflectionWithError grid desiredError
    |> Result.map Horizontal
    |> Result.onErr \NotFound ->
        findHorizontalReflectionWithError (columns grid) desiredError
        |> Result.map Vertical
    |> orCrash

columns : List (List elem) -> List (List elem)
columns = \grid -> columnsHelper grid [] 0
columnsHelper = \grid, cols, x ->
    when List.mapTry grid \row -> List.get row x is
        Ok col -> columnsHelper grid (List.append cols col) (x + 1)
        Err OutOfBounds -> cols

scoreReflection = \reflection ->
    when reflection is
        Horizontal row -> 100 * row
        Vertical column -> column

part1 : Input -> U64
part1 = \grids ->
    grids
    |> List.map \grid -> findReflectionWithError grid 0
    |> List.map scoreReflection
    |> List.sum

part2 : Input -> U64
part2 = \grids ->
    grids
    |> List.map \grid -> findReflectionWithError grid 1
    |> List.map scoreReflection
    |> List.sum

example : Str
example =
    """
    #.##..##.
    ..#.##.#.
    ##......#
    ##......#
    ..#.##.#.
    ..##..##.
    #.#.##.#.

    #...##..#
    #....#..#
    ..##..###
    #####.##.
    #####.##.
    ..##..###
    #....#..#
    """

expect
    answer = part1 (parse example)
    answer == 405

expect
    answer = part2 (parse example)
    answer == 400

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
