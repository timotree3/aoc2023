app "day1"
    packages { pf: "https://github.com/roc-lang/basic-cli/releases/download/0.7.0/bkGby8jb0tmZYsy2hg1E_B2QrCgcSTxdUlHtETwm5m4.tar.br" }
    imports [pf.Stdout, pf.Task.{ Task }, "../inputs/day1.txt" as input : Str]
    provides [main] to pf

part1 : Str -> U64
part1 = \in -> in
    |> Str.trim
    |> Str.split "\n"
    |> List.map parseLine1
    |> List.sum

parseLine1 : Str -> U64
parseLine1 = \line ->
    digits =
        Str.toUtf8 line
        |> List.keepOks asciiToDigit
    when digits is
        [first, .., last] | [first as last] -> first * 10 + last
        [] -> crash "no digits on line \(line)"

asciiToDigit : U8 -> Result U64 [NotDigit]
asciiToDigit = \b ->
    when Num.subChecked b '0' is
        Ok d if d < 10 -> Ok (Num.intCast d)
        _ -> Err NotDigit

part2 : Str -> U64
part2 = \in -> in
    |> Str.trim
    |> Str.split "\n"
    |> List.map parseLine2
    |> List.sum

parseLine2 : Str -> U64
parseLine2 = \line ->
    bytes = Str.toUtf8 line
    first =
        when findCardinal bytes Forwards is
            Ok n -> n
            Err NotFound -> crash "no Forwards cardinal found in line \(line)"
    last =
        when findCardinal bytes Backwards is
            Ok n -> n
            Err NotFound -> crash "bar"
    first * 10 + last

cardinals : List { name : List U8, val : U64 }
cardinals =
    words =
        [
            { name: "zero", val: 0 },
            { name: "one", val: 1 },
            { name: "two", val: 2 },
            { name: "three", val: 3 },
            { name: "four", val: 4 },
            { name: "five", val: 5 },
            { name: "six", val: 6 },
            { name: "seven", val: 7 },
            { name: "eight", val: 8 },
            { name: "nine", val: 9 },
        ]
        |> List.map \{ name, val } -> { name: Str.toUtf8 name, val }
    digits =
        List.range { start: At 0, end: Before 10 }
        |> List.map \n -> { name: Str.toUtf8 (Num.toStr n), val: n }
    List.concat words digits

eatCardinal : [Forwards, Backwards] -> (List U8 -> Result U64 [NotCardinal])
eatCardinal = \dir -> \l ->
        cardinals
        |> findOk
            (\{ name, val } ->
                if (hasAtBoundary dir) l name then
                    Ok val
                else
                    Err {})
        |> Result.mapErr \_ -> NotCardinal

findCardinal : List U8, [Forwards, Backwards] -> Result U64 [NotFound]
findCardinal = \l, dir ->
    sublists l dir |> findOk (eatCardinal dir)

main : Task {} I32
main =
    {} <- Stdout.line "part 1: \(Num.toStr (part1 input))" |> Task.await
    Stdout.line "part 2: \(Num.toStr (part2 input))"

# Stdout.line (testInput
# |> Str.trim
# |> Str.split "\n"
# |> List.map parseLine1
# |> List.map Num.toStr
# |> Str.joinWith "\n")#

part1TestInput =
    """
    1abc2
    pqr3stu8vwx
    a1b2c3d4e5f
    treb7uchet
    """

expect
    answer = part1 part1TestInput
    answer == 142

part2TestInput =
    """
    two1nine
    eightwothree
    abcone2threexyz
    xtwone3four
    4nineeightseven2
    zoneight234
    7pqrstsixteen
    oneight
    """

expect
    answer = part2 "abcone"
    answer == 11

expect
    answer = part2 part2TestInput
    answer == 281 + 18

# List utils

hasAtBoundary : [Forwards, Backwards] -> (List a, List a -> Bool) where a implements Eq
hasAtBoundary = \dir ->
    when dir is
        Forwards -> List.startsWith
        Backwards -> List.endsWith

lens : List a -> List Nat
lens = \l -> List.range { start: At 0, end: At (List.len l) } |> List.reverse

sublists : List a, [Forwards, Backwards] -> List (List a)
sublists = \l, dir ->
    lens l
    |> List.map \len ->
        when dir is
            Forwards -> List.takeLast l len
            Backwards -> List.takeFirst l len

findOk : List a, (a -> Result b *) -> Result b [NotFound]
findOk = \l, f ->
    List.walkUntil l (Err NotFound) \s, x ->
        when f x is
            Ok y -> Break (Ok y)
            Err _ -> Continue s
