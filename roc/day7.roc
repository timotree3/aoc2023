app "day7"
    packages { pf: "https://github.com/roc-lang/basic-cli/releases/download/0.7.0/bkGby8jb0tmZYsy2hg1E_B2QrCgcSTxdUlHtETwm5m4.tar.br" }
    imports [pf.Stdout, pf.Task.{ Task }, "../inputs/day7.txt" as input : Str]
    provides [main] to pf

Card : U8
Input : List { hand : List Card, bid : U64 }

parse : Str -> Input
parse = \inp ->
    inp
    |> Str.trim
    |> Str.split "\n"
    |> List.map parseLine

parseLine = \line ->
    when Str.split line " " is
        [hand, bid] ->
            { hand: parseHand hand, bid: Str.toU64 bid |> orCrash }

        _ -> crash "expected line to contain exactly two space-seperated values"

parseHand = \hand ->
    hand
    |> Str.toUtf8
    |> List.map parseCard

parseCard = \byte ->
    when byte is
        'A' -> 14
        'K' -> 13
        'Q' -> 12
        'J' -> 11
        'T' -> 10
        _ ->
            expect
                '2' <= byte && byte <= '9'

            2 + byte - '2'

ordLex = \a, b ->
    when a is
        EQ -> b
        GT | LT -> a

# Given two lists of equal length, compares them lexicographically
cmpLex = \a, b ->
    List.map2 a b Num.compare
    |> List.walk EQ ordLex

cmpHands = \a, b ->
    cmpLex (List.prepend a (handType a)) (List.prepend b (handType b))

groupBy : List a, (a, a -> Bool) -> List (List a)
groupBy = \l, pred ->
    List.walk l [] \groups, elem ->
        when List.last groups |> Result.try List.last is
            Ok prev if pred prev elem ->
                List.update groups (List.len groups - 1) \group ->
                    List.append group elem

            _ -> List.append groups [elem]

groupEq = \l -> groupBy l \a, b -> a == b

ifEmpty : List elem, List elem -> List elem
ifEmpty = \l, default ->
    if List.isEmpty l then
        default
    else
        l

handType : List Card -> U8
handType = \hand ->
    numJokers =
        hand
        |> List.countIf isJoker
    numOfEachKind =
        hand
        |> List.dropIf isJoker
        |> List.sortAsc
        |> groupEq
        |> List.map List.len
        |> List.sortDesc
        |> ifEmpty [0]
        |> List.update 0 \num -> num + numJokers

    when numOfEachKind is
        [5] -> 6
        [4, 1] -> 5
        [3, 2] -> 4
        [3, 1, 1] -> 3
        [2, 2, 1] -> 2
        [2, 1, 1, 1] -> 1
        [1, 1, 1, 1, 1] -> 0
        _ ->
            dbg
                numOfEachKind

            crash "unreachable"

part1 : Input -> U64
part1 = \players ->
    players
    |> List.sortWith \a, b -> cmpHands a.hand b.hand
    |> List.mapWithIndex \{ bid }, i -> bid * (Num.toU64 i + 1)
    |> List.sum

jacksToJokers = \players ->
    players
    |> List.map \{ hand, bid } -> {
        bid,
        hand: List.map hand jackToJoker,
    }

jackToJoker = \card ->
    when card is
        11 -> 1
        _ -> card

isJoker = \card -> card == 1

part2 : Input -> U64
part2 = \players ->
    players
    |> jacksToJokers
    |> part1

example : Str
example =
    """
    32T3K 765
    T55J5 684
    KK677 28
    KTJJT 220
    QQQJA 483
    """

expect
    answer = part1 (parse example)
    answer == 6440

expect
    answer = part2 (parse example)
    answer == 5905

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
