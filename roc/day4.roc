app "day2"
    packages { pf: "https://github.com/roc-lang/basic-cli/releases/download/0.7.0/bkGby8jb0tmZYsy2hg1E_B2QrCgcSTxdUlHtETwm5m4.tar.br" }
    imports [pf.Stdout, pf.Task.{ Task }, "../inputs/day4.txt" as input : Str]
    provides [main] to pf

part1 : Str -> Nat
part1 = \inp ->
    parseCards inp
    |> List.map pointValue
    |> List.sum

# powm1 m 0 = 0
# powm1 m (n + 1) = m ^ n
powm1 = \m, n ->
    when n is
        0 -> 0
        _ -> Num.powInt m (n - 1)

matchingNumbers = \{ winners, mine } ->
    mine
    |> Set.fromList
    |> Set.intersection (Set.fromList winners)
    |> Set.len

pointValue = \card -> powm1 2 (matchingNumbers card)

parseCards = \inp ->
    inp
    |> Str.trim
    |> Str.split "\n"
    |> List.map parseCard

parseCard = \line ->
    { before, after } =
        line
        |> Str.splitFirst ": "
        |> orCrash
        |> .after
        |> Str.splitFirst " | "
        |> orCrash
    { winners: parseNums before, mine: parseNums after }

parseNums = \nums ->
    nums
    |> Str.split " "
    |> List.map Str.trim
    |> List.dropIf Str.isEmpty
    |> List.mapTry Str.toU64
    |> orCrash

part2 : Str -> U64
part2 = \inp ->
    parseCards inp
    |> List.map matchingNumbers
    |> countCopies
    |> List.sum

countCopies = \cards ->
    List.walkWithIndex cards (List.repeat 1 (List.len cards)) distributeCopies

distributeCopies = \copies, numCards, i ->
    additionalCopies =
        copies
        |> List.get i
        |> Result.withDefault 0
    updateIndices
        copies
        (List.range { start: At (i + 1), end: Length numCards })
        \count -> count + additionalCopies

updateIndices = \l, indices, f ->
    List.walk indices l \oldList, i ->
        List.update oldList i f

example : Str
example =
    """
    Card 1: 41 48 83 86 17 | 83 86  6 31 17  9 48 53
    Card 2: 13 32 20 16 61 | 61 30 68 82 17 32 24 19
    Card 3:  1 21 53 59 44 | 69 82 63 72 16 21 14  1
    Card 4: 41 92 73 84 69 | 59 84 76 51 58  5 54 83
    Card 5: 87 83 26 28 32 | 88 30 70 12 93 22 82 36
    Card 6: 31 18 13 56 72 | 74 77 10 23 35 67 36 11
    """

expect
    answer = parseCard "Card 3:  1 21 53 59 44 | 69 82 63 72 16 21 14  1"
    answer == { winners: [1, 21, 53, 59, 44], mine: [69, 82, 63, 72, 16, 21, 14, 1] }

expect
    answer = part1 example
    answer == 13

expect
    answer = part2 example
    answer == 30

expect
    answer =
        parseCards example
        |> List.map matchingNumbers
        |> countCopies
    answer == [1, 2, 4, 8, 14, 1]

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
