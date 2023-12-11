app "day10"
    packages { pf: "https://github.com/roc-lang/basic-cli/releases/download/0.7.0/bkGby8jb0tmZYsy2hg1E_B2QrCgcSTxdUlHtETwm5m4.tar.br" }
    imports [pf.Stdout, pf.Task.{ Task }, "../inputs/day10.txt" as input : Str]
    provides [main] to pf

Tile : [NS, EW, NE, NW, SW, SE, Ground, Animal]
Direction : [N, S, E, W]
Input : List (List Tile)
Point : (Nat, Nat)

parse : Str -> Input
parse = \inp ->
    inp
    |> Str.trim
    |> Str.split "\n"
    |> List.map parseLine

parseLine = \line ->
    line
    |> Str.toUtf8
    |> List.map parseTile

parseTile = \byte ->
    when byte is
        '|' -> NS
        '-' -> EW
        'L' -> NE
        'J' -> NW
        '7' -> SW
        'F' -> SE
        '.' -> Ground
        'S' -> Animal
        _ -> crash "unexpected byte in input"

get = \grid, (x, y) ->
    grid
    |> List.get y
    |> orCrash
    |> List.get x
    |> orCrash

set = \grid, (x, y), val ->
    grid
    |> List.update y \row ->
        List.set row x val

find = \grid, val ->
    res =
        findFirstOk grid \row ->
            findFirstOk row \tile ->
                if tile == val then
                    Ok IsNeedle
                else
                    Err NotNeedle
    (y, (x, IsNeedle)) <- Result.map res
    (x, y)

findFirstOk : List a, (a -> Result b *) -> Result (Nat, b) [NotFound]
findFirstOk = \l, f ->
    (pos, res) = List.walkUntil l (0, Err NotFound) \(i, _), elem ->
        when f elem is
            Ok v -> Break (i, Ok v)
            Err _ -> Continue (i + 1, Err NotFound)
    v <- Result.map res
    (pos, v)

stepDirection = \(x, y), dir ->
    when dir is
        N -> (x, Num.subWrap y 1)
        S -> (x, y + 1)
        E -> (x + 1, y)
        W -> (Num.subWrap x 1, y)

followPipe : Input, Point, Direction -> Result (Point, Direction) [NoPipe Tile]
followPipe = \grid, (x, y), dir ->
    nextPoint = stepDirection (x, y) dir
    nextDirectionRes =
        when (dir, get grid nextPoint) is
            (N, NS) | (E, NW) | (W, NE) -> Ok N
            (S, NS) | (E, SW) | (W, SE) -> Ok S
            (N, SE) | (S, NE) | (E, EW) -> Ok E
            (N, SW) | (S, NW) | (W, EW) -> Ok W
            (_, tile) -> Err (NoPipe tile)
    nextDirection <- Result.map nextDirectionRes
    (nextPoint, nextDirection)

iterTry : Result a b, (a -> Result a b) -> (List a, b)
iterTry = \r, f -> iterTryHelper r f []

iterTryHelper : Result a b, (a -> Result a b), List a -> (List a, b)
iterTryHelper = \r, f, l ->
    when r is
        Ok v -> iterTryHelper (f v) f (List.append l v)
        Err e -> (l, e)

walk : Input, Point, Direction -> Result (List (Point, Direction)) [DeadEnd]
walk = \grid, point, direction ->
    (path, NoPipe tile) = iterTry (Ok (point, direction)) \(p, dir) ->
        followPipe grid p dir
    when tile is
        Animal -> Ok path # We got back to the start!
        _ -> Err DeadEnd

part1 : Input -> Nat
part1 = \grid ->
    animalPos = find grid Animal |> orCrash
    (_, path) =
        [N, S, E, W]
        |> findFirstOk \dir -> walk grid animalPos dir
        |> orCrash

    # e.g.
    # S7
    # LJ
    # pathLen == 4
    # answer == 2
    List.len path // 2

hasSouthEdge = \tile ->
    when tile is
        NS | SE | SW -> Bool.true
        NE | NW | EW | Ground -> Bool.false
        Animal -> crash "expected animal to be replaced with pipe"

rowInnies : List Tile, (Nat -> Bool) -> Set Nat
rowInnies = \row, inPath ->
    (finalInnies, _) = List.walkWithIndex row (Set.empty {}, 0) \(innies, numSouthEdges), tile, x ->
        newInnies =
            if numSouthEdges % 2 == 1 && !(inPath x) then
                Set.insert innies x
            else
                innies
        newNumSouthEdges =
            if hasSouthEdge tile && inPath x then
                numSouthEdges + 1
            else
                numSouthEdges

        (newInnies, newNumSouthEdges)
    dbg
        finalInnies

    finalInnies

part2 : Input -> Nat
part2 = \grid ->
    animalPos = find grid Animal |> orCrash
    (_, path) =
        [N, S, E, W]
        |> findFirstOk \dir -> walk grid animalPos dir
        |> orCrash

    animalAsPipe =
        when path is
            [(_, S), .., (_, W)] -> SE
            [(_, S), .., (_, S)] -> NS
            [(_, S), .., (_, E)] -> SW
            [(_, N), .., (_, W)] -> NE
            [(_, N), .., (_, N)] -> NS
            [(_, N), .., (_, E)] -> NW
            [(_, W), .., (_, N)] -> SW
            [(_, W), .., (_, W)] -> EW
            [(_, W), .., (_, S)] -> NW
            [(_, E), .., (_, N)] -> SE
            [(_, E), .., (_, E)] -> EW
            [(_, E), .., (_, S)] -> NE
            _ -> crash "expected path to leave and arrive at animal from different directions"

    newGrid = set grid animalPos animalAsPipe

    pathSet = Set.fromList (path |> List.map .0)
    newGrid
    |> List.mapWithIndex \row, y ->
        rowInnies row \x -> Set.contains pathSet (x, y)
        |> Set.map \x -> (x, y)
    |> List.walk (Set.empty {}) Set.union
    |> Set.len

example1 =
    """
    -L|F7
    7S-7|
    L|7||
    -L-J|
    L|-JF
    """

example2 =
    """
    7-F7-
    .FJ|7
    SJLL7
    |F--J
    LJ.LJ
    """

expect
    answer = part1 (parse example1)
    answer == 4

expect
    answer = part1 (parse example2)
    answer == 8

example3 =
    """
    ...........
    .S-------7.
    .|F-----7|.
    .||.....||.
    .||.....||.
    .|L-7.F-J|.
    .|..|.|..|.
    .L--J.L--J.
    ...........
    """

expect
    answer = part2 (parse example3)
    answer == 4

example4 =
    """
    .F----7F7F7F7F-7....
    .|F--7||||||||FJ....
    .||.FJ||||||||L7....
    FJL7L7LJLJ||LJ.L-7..
    L--J.L7...LJS7F-7L7.
    ....F-J..F7FJ|L7L7L7
    ....L7.F7||L7|.L7L7|
    .....|FJLJ|FJ|F7|.LJ
    ....FJL-7.||.||||...
    ....L---J.LJ.LJLJ...
    """

expect
    answer = part2 (parse example4)
    answer == 8

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
