app "day11"
    packages { pf: "https://github.com/roc-lang/basic-cli/releases/download/0.8.1/x8URkvfyi9I0QhmVG98roKBUs_AZRkLFwFJVJ3942YA.tar.br" }
    imports [pf.Stdout, pf.Task.{ Task }, "../inputs/day11.txt" as input : Str]
    provides [main] to pf

Tile : [Empty, Galaxy Point]
Input : List (List Tile)
Point : (U64, U64)

parse : Str -> Input
parse = \inp ->
    inp
    |> Str.trim
    |> Str.split "\n"
    |> List.mapWithIndex parseLine

parseLine = \line, y ->
    line
    |> Str.toUtf8
    |> List.mapWithIndex \byte, x -> parseTile byte (x, y)

parseTile = \byte, point ->
    when byte is
        '.' -> Empty
        '#' -> Galaxy point
        _ -> crash "unexpected byte in input"

columns : List (List elem) -> List (List elem)
columns = \grid -> columnsHelper grid [] 0
columnsHelper = \grid, cols, x ->
    when List.mapTry grid \row -> List.get row x is
        Ok col -> columnsHelper grid (List.append cols col) (x + 1)
        Err OutOfBounds -> cols

lineEmpty = \line -> List.all line \t -> t == Empty

boolToNum = \b -> if b then 1 else 0

updateCoords = \f ->
    \tile ->
        when tile is
            Empty -> Empty
            Galaxy p -> Galaxy (f p)

expandEmptyRows = \grid, expandFactor ->
    shiftDownAmounts =
        grid
        |> List.map lineEmpty
        |> List.map boolToNum
        |> List.map \n -> n * (expandFactor - 1)
        |> prefixSum
    List.map2 grid shiftDownAmounts \row, shiftDownAmount ->
        List.map row (updateCoords \(x, y) -> (x, y + shiftDownAmount))

expandEmptyColumns = \grid, expandFactor ->
    columnar = columns grid
    shiftRightAmounts =
        columnar
        |> List.map lineEmpty
        |> List.map boolToNum
        |> List.map \n -> n * (expandFactor - 1)
        |> prefixSum
    shiftedColumnar = List.map2 columnar shiftRightAmounts \col, shiftRightAmount ->
        List.map col (updateCoords \(x, y) -> (x + shiftRightAmount, y))
    columns shiftedColumnar

manhattanDistance = \(x1, y1), (x2, y2) ->
    Num.absDiff x1 x2 + Num.absDiff y1 y2

solve : Input, U64 -> U64
solve = \grid, expandFactor ->
    galaxies =
        grid
        |> expandEmptyRows expandFactor
        |> expandEmptyColumns expandFactor
        |> List.join
        |> List.keepOks \tile ->
            when tile is
                Galaxy point -> Ok point
                Empty -> Err Empty

    galaxies
    |> List.map \g1 ->
        galaxies
        |> List.map \g2 ->
            manhattanDistance g1 g2
        |> List.sum
    |> List.sum
    |> Num.divTrunc 2

part1 : Input -> U64
part1 = \grid ->
    solve grid 2

part2 : Input -> U64
part2 = \grid ->
    solve grid 1_000_000

example =
    """
    ...#......
    .......#..
    #.........
    ..........
    ......#...
    .#........
    .........#
    ..........
    .......#..
    #...#.....
    """

expect
    answer = part1 (parse example)
    answer == 374

expect
    answer = solve (parse example) 10
    answer == 1030

expect
    answer = solve (parse example) 100
    answer == 8410

main : Task {} I32
main =
    {} <- Stdout.line "Part 1: \(Num.toStr (part1 (parse input)))" |> Task.await
    Stdout.line "Part 2: \(Num.toStr (part2 (parse input)))"

prefixSum : List (Num a) -> List (Num a)
prefixSum = \l ->
    (sums, total) = walkMap l 0 \acc, elem ->
        (acc, acc + elem)
    List.append sums total
walkMap = \l, state, f ->
    List.walk l ([], state) \(mappedSoFar, oldState), elem ->
        (mapped, newState) = f oldState elem
        (List.append mappedSoFar mapped, newState)

