app "day14"
    packages { pf: "https://github.com/roc-lang/basic-cli/releases/download/0.7.0/bkGby8jb0tmZYsy2hg1E_B2QrCgcSTxdUlHtETwm5m4.tar.br" }
    imports [pf.Stdout, pf.Task.{ Task }, "../inputs/day14.txt" as input : Str]
    provides [main] to pf

Grid : List (List U8)

parse : Str -> Grid
parse = \inp ->
    inp
    |> Str.trim
    |> Str.split "\n"
    |> List.map Str.toUtf8

## Shift all rocks left to the nearest wall, stacking with other rocks
backshiftRocks = \row ->
    row
    |> splitOn '#'
    |> List.map List.sortDesc
    |> joinWith '#'

expect 'O' > '.'

scoreColumn = \column ->
    column
    |> List.mapWithIndex \tile, y ->
        if tile == 'O' then
            List.len column - y
        else
            0
    |> List.sum

part1 : Grid -> Nat
part1 = \grid ->
    grid
    |> columns
    |> List.map backshiftRocks
    |> List.map scoreColumn
    |> List.sum

spinCycle = \grid ->
    # North, West, South, East
    grid
    |> columns
    |> List.map backshiftRocks
    |> columns
    |> List.map backshiftRocks
    |> List.reverse
    |> columns
    |> List.map backshiftRocks
    |> columns
    |> List.reverse
    |> List.map List.reverse
    |> List.map backshiftRocks
    |> List.map List.reverse

iterateWithPeriodDetection : state, (state -> state), Nat -> state where state implements Eq
iterateWithPeriodDetection = \start, f, fuel1 ->
    (periodicElem, fuel2) = findPeriodicElement start f fuel1
    if fuel2 == 0 then
        periodicElem
    else
        (reocurrence, fuel3) = iterateUntil (f periodicElem) f (\x -> x == periodicElem) (fuel2 - 1)

        period = fuel2 - fuel3
        fuel4 = fuel3 % period

        iterate reocurrence f fuel4

iterate = \x, f, n ->
    if n == 0 then
        x
    else
        iterate (f x) f (n - 1)

findPeriodicElement = \start, next, fuel ->
    tortoiseHare start (next start) next fuel
tortoiseHare = \tortoise, hare, next, fuel ->
    if fuel == 0 || tortoise == hare then
        (tortoise, fuel)
    else
        tortoiseHare (next tortoise) (next (next hare)) next (fuel - 1)

iterateUntil = \start, next, stop, fuel ->
    if fuel == 0 || stop start then
        (start, fuel)
    else
        iterateUntil (next start) next stop (fuel - 1)

part2 : Grid -> Nat
part2 = \grid ->
    grid
    |> iterateWithPeriodDetection spinCycle 1_000_000_000
    |> columns
    |> List.map scoreColumn
    |> List.sum

example : Str
example =
    """
    O....#....
    O.OO#....#
    .....##...
    OO.#O....O
    .O.....O#.
    O.#..O.#.#
    ..O..#O..O
    .......O..
    #....###..
    #OO..#....
    """

exampleNorth =
    """
    OOOO.#.O..
    OO..#....#
    OO..O##..O
    O..#.OO...
    ........#.
    ..#....#.#
    ..O..#.O.O
    ..O.......
    #....###..
    #....#....
    """

example1 =
    """
    .....#....
    ....#...O#
    ...OO##...
    .OO#......
    .....OOO#.
    .O#...O#.#
    ....O#....
    ......OOOO
    #...O###..
    #..OO#....
    """

example3 =
    """
    .....#....
    ....#...O#
    .....##...
    ..O#......
    .....OOO#.
    .O#...O#.#
    ....O#...O
    .......OOO
    #...O###.O
    #.OOO#...O
    """

expect
    answer = part1 (parse example)
    answer == 136

expect
    answer =
        "O.#..O.#.OO."
        |> Str.toUtf8
        |> backshiftRocks
        |> scoreColumn
    answer == 12 + 9 + 4 + 3

printGrid = \grid ->
    grid
    |> List.mapTry Str.fromUtf8
    |> orCrash
    |> Str.joinWith "\n"

expect
    answer = parse example |> spinCycle |> printGrid
    answer == example1

expect
    answer = parse example |> iterate spinCycle 3 |> printGrid
    answer == example3

expect
    answer = parse example |> columns |> List.map backshiftRocks |> columns |> printGrid
    answer == exampleNorth

expect
    answer = part2 (parse example)
    answer == 64

main : Task {} I32
main =
    {} <- Stdout.line "Part 1: \(Num.toStr (part1 (parse input)))" |> Task.await
    Stdout.line "Part 2: \(Num.toStr (part2 (parse input)))"

# Helper functions copied from previous days

orCrash : Result v e -> v where e implements Inspect
orCrash = \r ->
    when r is
        Ok v -> v
        Err e ->
            dbg
                e

            crash "orCrash encounted Err"

splitOn : List elem, elem -> List (List elem) where elem implements Eq
splitOn = \list, delimiter ->
    if List.isEmpty list then
        []
    else
        List.walk list [[]] \segmentsSoFar, elem ->
            if elem == delimiter then
                List.append segmentsSoFar []
            else
                List.update segmentsSoFar (List.len segmentsSoFar - 1) \segment ->
                    List.append segment elem

expect
    answer = splitOn [1, 2, 3, 0, 0, 4, 0, 5, 0] 0
    answer == [[1, 2, 3], [], [4], [5], []]

joinWith : List (List elem), elem -> List elem
joinWith = \lists, separator ->
    lists
    |> List.intersperse [separator]
    |> List.join

columns : List (List elem) -> List (List elem)
columns = \grid -> columnsHelper grid [] 0
columnsHelper = \grid, cols, x ->
    when List.mapTry grid \row -> List.get row x is
        Ok col -> columnsHelper grid (List.append cols col) (x + 1)
        Err OutOfBounds -> cols
