app "day3"
    packages { pf: "https://github.com/roc-lang/basic-cli/releases/download/0.7.0/bkGby8jb0tmZYsy2hg1E_B2QrCgcSTxdUlHtETwm5m4.tar.br" }
    imports [pf.Stdout, pf.Task.{ Task }, "../inputs/day3.txt" as input : Str]
    provides [main] to pf

Grid : List (List GridCell)
GridCell : [Digit, Star { count : U8, power : U64 }, Symbol, Dot]
Numeral : { x : Nat, y : Nat, len : Nat, val : U64 }

parseNums : Str -> List Numeral
parseNums = \inp -> inp
    |> Str.trim
    |> Str.split "\n"
    |> List.mapWithIndex
        (\line, y -> # ask about contrained record types
            List.map (extractNums line) \{ x, len, val } -> { x, y, len, val })
    |> List.join

parseGrid : Str -> Grid
parseGrid = \inp -> inp
    |> Str.trim
    |> Str.split "\n"
    |> List.map \line -> line
        |> Str.toUtf8
        |> List.map \byte ->
            when byte is
                '.' -> Dot
                '*' -> Star { count: 0, power: 1 }
                b if '0' <= b && b <= '9' -> Digit
                _ -> Symbol

prefixSum : List (Num a) -> List (Num a)
prefixSum = \l ->
    (sums, total) = walkMap l 0 \acc, elem ->
        (acc, acc + elem)
    List.append sums total

groupBy : List a, (a, a -> Bool) -> List (List a)
groupBy = \l, pred ->
    List.walk l [] \groups, elem ->
        when List.last groups |> Result.try List.last is
            Ok prev if pred prev elem ->
                List.update groups (List.len groups - 1) \group ->
                    List.append group elem

            _ -> List.append groups [elem]

groupByKey = \l, key ->
    groupBy l \prev, elem -> key prev == key elem

isAsciiDigit = \byte -> '0' <= byte && byte <= '9'

walkMap = \l, state, f ->
    List.walk l ([], state) \(mappedSoFar, oldState), elem ->
        (mapped, newState) = f oldState elem
        (List.append mappedSoFar mapped, newState)

extractNums = \line ->
    groups =
        line
        |> Str.toUtf8
        |> groupByKey isAsciiDigit
    offsets =
        groups
        |> List.map List.len
        |> prefixSum
    results = List.map2 groups offsets \group, offset ->
        val <- fromAsciiDigits group |> Result.map
        { x: offset, len: List.len group, val }
    List.keepOks results \r -> r

fromAsciiDigits = \digits ->
    Str.fromUtf8 digits |> orCrash |> Str.toU64

expect
    prefixes = prefixSum [3, 0, 0]
    prefixes == [0, 3, 3, 3]

expect
    nums = extractNums ".#755."
    nums == [{ x: 2, len: 3, val: 755 }]

expect
    nums = extractNums "467..114.."
    nums
    == [
        { x: 0, len: 3, val: 467 },
        { x: 5, len: 3, val: 114 },
    ]

expect
    nums = parseNums example
    nums
    == [
        { x: 0, y: 0, len: 3, val: 467 },
        { x: 5, y: 0, len: 3, val: 114 },
        { x: 2, y: 2, len: 2, val: 35 },
        { x: 6, y: 2, len: 3, val: 633 },
        { x: 0, y: 4, len: 3, val: 617 },
        { x: 7, y: 5, len: 2, val: 58 },
        { x: 2, y: 6, len: 3, val: 592 },
        { x: 6, y: 7, len: 3, val: 755 },
        { x: 1, y: 9, len: 3, val: 664 },
        { x: 5, y: 9, len: 3, val: 598 },
    ]

neighbors = \x, y -> [
    (Num.subWrap x 1, Num.subWrap y 1),
    (Num.subWrap x 1, y),
    (Num.subWrap x 1, y + 1),
    (x, Num.subWrap y 1),
    (x, y + 1),
    (x + 1, Num.subWrap y 1),
    (x + 1, y),
    (x + 1, y + 1),
]

numeralNeighbors = \{ x: left, y, len } ->
    List.range { start: At left, end: Length len }
    |> List.joinMap \x -> neighbors x y

symbolAt = \grid, x, y ->
    cell = List.get grid y |> Result.try \row -> List.get row x
    when cell is
        Ok Symbol -> Bool.true
        Ok (Star _) -> Bool.true
        _ -> Bool.false

numHasSymbol = \grid -> \num ->
        numeralNeighbors num |> List.any \(x, y) -> symbolAt grid x y

part1 : Str -> U64
part1 = \inp ->
    grid = parseGrid inp
    parseNums inp
    |> List.keepIf (numHasSymbol grid)
    |> List.map \{ val } -> val
    |> List.sum

exampleGrid = parseGrid example

expect
    nums = parseNums example |> List.keepIf (numHasSymbol exampleGrid)
    nums
    == [
        { x: 0, y: 0, len: 3, val: 467 },
        { x: 2, y: 2, len: 2, val: 35 },
        { x: 6, y: 2, len: 3, val: 633 },
        { x: 0, y: 4, len: 3, val: 617 },
        { x: 2, y: 6, len: 3, val: 592 },
        { x: 6, y: 7, len: 3, val: 755 },
        { x: 1, y: 9, len: 3, val: 664 },
        { x: 5, y: 9, len: 3, val: 598 },
    ]

expect !(isAsciiDigit ('9' + 1))
expect !(isAsciiDigit ('0' - 1))

expect (numHasSymbol exampleGrid) { x: 0, y: 0, len: 3, val: 467 }
expect symbolAt exampleGrid 3 1

touchStar = \grid, x, y, val ->
    List.update grid y \row ->
        List.update row x \cell ->
            when cell is
                Star { count, power } -> Star { count: count + 1, power: power * val }
                _ -> cell

touchStars = \grid, nums ->
    List.walk nums grid \oldGrid, num -> numeralNeighbors num
        |> Set.fromList
        |> Set.walk oldGrid \oldGrid2, (x, y) ->
            touchStar oldGrid2 x y num.val

part2 : Str -> U64
part2 = \inp -> parseGrid inp
    |> touchStars (parseNums inp)
    |> List.join
    |> List.keepOks \cell ->
        when cell is
            Star { count: 2, power } -> Ok power
            _ -> Err {}
    |> List.sum

expect
    stars =
        parseGrid example
        |> touchStars (parseNums example)
        |> List.join
        |> List.keepIf \cell ->
            when cell is
                Star _ -> Bool.true
                _ -> Bool.false
    stars == [Star { count: 2, power: 467 * 35 }, Star { count: 1, power: 617 }, Star { count: 2, power: 755 * 598 }]

example : Str
example =
    """
    467..114..
    ...*......
    ..35..633.
    ......#...
    617*......
    .....+.58.
    ..592.....
    .....#755.
    ...$.*....
    .664.598..
    """

expect
    answer = part1 example
    answer == 4361

expect
    answer = part2 example
    answer == 467835

# reprint : List Numeral -> Str
# reprint = \l ->
#     {acc} = List.walk l {x: 0, y: 0, acc: ""} \old, numeral ->
#         (newlines, cursorX) =
#             if old.y < numeral.y then
#                 (Str.repeat "\n" (numeral.y - old.y), 0)
#             else
#                 ("", old.x)
#         dots = Str.repeat "." (numeral.x - cursorX)

#         {x: numeral.x + numeral.len, y: numeral.y, acc: "\(old.acc)\(newlines)\(dots)\(Num.toStr numeral.val)"}
#     acc

# main : Task {} I32
# main =
#     {nums, grid} = parseNums input
#     nums
#         |> List.keepIf (numHasSymbol grid)
#         |> reprint
#         |> Stdout.line

main : Task {} I32
main =
    Stdout.line
        """
        Part 1: \(Num.toStr (part1 input))
        Part 2: \(Num.toStr (part2 input))
        """

orCrash : Result a * -> a
orCrash = \r ->
    when r is
        Ok v -> v
        Err _ -> crash "orCrash encounted Err"
