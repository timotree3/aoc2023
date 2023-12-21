app "day16"
    packages {
        pf: "https://github.com/roc-lang/basic-cli/releases/download/0.7.0/bkGby8jb0tmZYsy2hg1E_B2QrCgcSTxdUlHtETwm5m4.tar.br",
        array2d: "https://github.com/mulias/roc-array2d/releases/download/v0.1.1/gvYudeXPZL33PDh5jRxXOPbeaQV5kLZAsgecc68HBOA.tar.br",
    }
    imports [array2d.Array2D.{ Array2D }, pf.Stdout, pf.Task.{ Task }, "../inputs/day16.txt" as input : Str]
    provides [main] to pf

Grid : Array2D Tile
Tile : [Diagonal, AntiDiag, Vertical, Horizontal, Empty]

parse : Str -> Grid
parse = \inp ->
    inp
    |> Str.trim
    |> Str.split "\n"
    |> List.map parseLine
    |> Array2D.fromExactLists
    |> orCrash

parseLine = \line ->
    line
    |> Str.toUtf8
    |> List.map parseTile

parseTile = \byte ->
    when byte is
        '.' -> Empty
        '\\' -> Diagonal
        '/' -> AntiDiag
        '|' -> Vertical
        '-' -> Horizontal
        _ -> crash "unexpected byte in grid"

LightPath : Set (Array2D.Index, Direction)
Direction : [Left, Right, Up, Down]

raycast : LightPath, Grid, Array2D.Index, Direction -> LightPath
raycast = \path, grid, position, direction ->
    if path |> Set.contains (position, direction) then
        path
    else
        when Array2D.get grid position is
            Ok tile ->
                newDirections = bouncesTowards tile direction
                newDirections
                |> List.walk (Set.insert path (position, direction)) \updatedPath, newDirection ->
                    raycast updatedPath grid (step position newDirection) newDirection

            Err OutOfBounds ->
                path

bouncesTowards : Tile, Direction -> List Direction
bouncesTowards = \tile, direction ->
    when (tile, direction) is
        (Empty, _)
        | (Horizontal, Right)
        | (Horizontal, Left)
        | (Vertical, Up)
        | (Vertical, Down) -> [direction]

        (Diagonal, Right) | (AntiDiag, Left) -> [Down]
        (Diagonal, Left) | (AntiDiag, Right) -> [Up]
        (Diagonal, Down) | (AntiDiag, Up) -> [Right]
        (Diagonal, Up) | (AntiDiag, Down) -> [Left]
        (Horizontal, Up) | (Horizontal, Down) -> [Left, Right]
        (Vertical, Left) | (Vertical, Right) -> [Up, Down]
        _ -> crash "this `when` is exhaustive.."

step = \{ x, y }, direction ->
    # Array2D uses X and Y in swapped senses
    when direction is
        Up -> { x: x |> Num.subWrap 1, y }
        Down -> { x: x + 1, y }
        Left -> { x, y: y |> Num.subWrap 1 }
        Right -> { x, y: y + 1 }

part1 : Grid -> Nat
part1 = \grid ->
    raycast (Set.empty {}) grid { x: 0, y: 0 } Right
    |> Set.map \(coords, _) -> coords
    |> \path ->
        energized =
            grid
            |> Array2D.mapWithIndex \_, { x, y } ->
                if Set.contains path { x, y } then
                    "#"
                else
                    "."
            |> Array2D.joinWith "" "\n"
        dbg
            energized

        path
    |> Set.len

part2 : Grid -> Nat
part2 = \x ->
    crash "todo"

example : Str
example =
    """
    .|...\\....
    |.-.\\.....
    .....|-...
    ........|.
    ..........
    .........\\
    ..../.\\\\..
    .-.-/..|..
    .|....-|.\\
    ..//.|....    
    """

expect
    answer = part1 (parse example)
    answer == 46

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
