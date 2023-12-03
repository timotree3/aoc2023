app "day2"
    packages { pf: "https://github.com/roc-lang/basic-cli/releases/download/0.7.0/bkGby8jb0tmZYsy2hg1E_B2QrCgcSTxdUlHtETwm5m4.tar.br" }
    imports [pf.Stdout, pf.Task.{ Task }, "../inputs/day2.txt" as input : Str]
    provides [main] to pf


part1 : Str -> U64
part1 = \in -> in
    |> parseGames
    |> List.keepIf possible
    |> List.map (\{id} -> id)
    |> List.sum

part2 : Str -> U64
part2 = \in -> in
    |> parseGames
    |> List.map gamePower
    |> List.sum

example : Str
example =
"""
Game 1: 3 blue, 4 red; 1 red, 2 green, 6 blue; 2 green
Game 2: 1 blue, 2 green; 3 green, 4 blue, 1 red; 1 green, 1 blue
Game 3: 8 green, 6 blue, 20 red; 5 blue, 4 red, 13 green; 5 green, 1 red
Game 4: 1 green, 3 red, 6 blue; 3 green, 6 red; 3 green, 15 blue, 14 red
Game 5: 6 red, 1 blue, 3 green; 2 blue, 1 red, 2 green
"""

expect
    answer = part1 example
    answer == 8

expect
    answer = part2 example
    answer == 2286
    
Game : {
    id : U64,
    samples : List Sample
}

Sample : {
    red : U64,
    green : U64,
    blue : U64,
}

# mkS : {red ? U64, green ? U64, blue ? U64} -> Sample
mkS = \{red ? 0, green ? 0, blue ? 0} -> {red, green, blue}

zeroS = mkS {}

addS : Sample, Sample -> Sample
addS = \a, b -> {
    red: a.red + b.red,
    green: a.green + b.green,
    blue: a.blue + b.blue,
}

maxS : Sample, Sample -> Sample
maxS = \a, b -> {
    red: Num.max a.red b.red,
    green: Num.max a.green b.green,
    blue: Num.max a.blue b.blue,
}

parseGames : Str -> List Game
parseGames = \in -> in
    |> Str.trim
    |> Str.split "\n"
    |> List.map parseGame

parseGame : Str -> Game
parseGame = \line ->
    expect Str.startsWith line "Game "
    {before: id, after: rest} = line
        |> Str.replaceFirst "Game " ""
        |> Str.splitFirst ": "
        |> orCrash
    {id: Str.toU64 id |> orCrash, samples: Str.split rest "; " |> List.map parseSample}


parseSample : Str -> Sample
parseSample = \s ->
    Str.split s ", "
        |> List.map parseColor
        |> List.walk zeroS addS

parseColor : Str -> Sample
parseColor = \s ->
    {before, after: colorName} = Str.splitFirst s " " |> orCrash
    qty = Str.toU64 before |> orCrash
    when colorName is
        "red" -> mkS {red: qty}
        "green" -> mkS {green: qty}
        "blue" -> mkS {blue: qty}
        _ -> crash "unexpected colorName \(colorName)"

expect
    answer = parseGame "Game 12: 30 blue, 40 red; 10 red, 20 green, 60 blue; 20 green"
    answer == {id: 12, samples: [{red: 40, blue: 30, green: 0}, {red: 10, green: 20, blue: 60}, {red: 0, green: 20, blue: 0}]}

possible : Game -> Bool
possible = \{samples} ->
    List.all samples \{red, green, blue} ->
        red <= 12 && green <= 13 && blue <= 14

gamePower : Game -> U64
gamePower = \{samples} ->
    {red, green, blue} = List.walk samples zeroS maxS
    red * green * blue


main : Task {} I32
main = Stdout.line
    """
    Part 1: \(Num.toStr (part1 input))
    Part 2: \(Num.toStr (part2 input))
    """

orCrash : Result a * -> a
orCrash = \r ->
    when r is
        Ok v -> v
        Err _ -> crash "orCrash encounted Err"
