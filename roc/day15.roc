app "day15"
    packages { pf: "https://github.com/roc-lang/basic-cli/releases/download/0.7.0/bkGby8jb0tmZYsy2hg1E_B2QrCgcSTxdUlHtETwm5m4.tar.br" }
    imports [pf.Stdout, pf.Task.{ Task }, "../inputs/day15.txt" as input : Str]
    provides [main] to pf

hashString = \string ->
    List.walk string 0 \state, byte -> state |> Num.addWrap byte |> Num.mulWrap 17

part1 : Str -> Nat
part1 = \inp ->
    inp
    |> Str.trim
    |> Str.split ","
    |> List.map Str.toUtf8
    |> List.map hashString
    |> List.map Num.toNat
    |> List.sum

Step : { label : List U8, op : [Remove, Insert U8] }

parseStep : Str -> Step
parseStep = \step ->
    when Str.splitFirst step "=" is
        Ok { before, after } ->
            { label: before |> Str.toUtf8, op: Insert (Str.toU8 after |> orCrash) }

        Err NotFound ->
            expect
                Str.endsWith step "-"

            { label: Str.replaceLast step "-" "" |> Str.toUtf8, op: Remove }

Boxes : List (Dict (List U8) U8)

emptyBoxes = List.repeat (Dict.empty {}) 256

runStep : Boxes, Step -> Boxes
runStep = \boxes, { label, op } ->
    hash = hashString label
    boxes
    |> List.update (Num.toNat hash) \box ->
        when op is
            Remove ->
                shiftRemove box label

            Insert focal ->
                Dict.insert box label focal

scoreBoxes : Boxes -> Nat
scoreBoxes = \boxes ->
    boxes
    |> List.mapWithIndex \box, boxNumber ->
        box
        |> Dict.toList
        |> List.mapWithIndex \(_, focal), slotNumber ->
            (1 + boxNumber) * (1 + slotNumber) * (Num.toNat focal)
        |> List.sum
    |> List.sum

part2 : Str -> Nat
part2 = \inp ->
    steps =
        inp
        |> Str.trim
        |> Str.split ","
        |> List.map parseStep
    steps
    |> List.walk emptyBoxes runStep
    |> scoreBoxes

example = "rn=1,cm-,qp=3,cm=2,qp-,pc=4,ot=9,ab=5,pc-,pc=6,ot=7"

expect
    answer = part1 example
    answer == 1320

expect
    answer = part2 example
    answer == 145

main : Task {} I32
main =
    {} <- Stdout.line "Part 1: \(Num.toStr (part1 input))" |> Task.await
    Stdout.line "Part 2: \(Num.toStr (part2 input))"

shiftRemove : Dict key val, key -> Dict key val
shiftRemove = \dict, key ->
    dict
    |> Dict.toList
    |> List.dropIf \(k, _) -> k == key
    |> Dict.fromList

orCrash : Result v e -> v where e implements Inspect
orCrash = \r ->
    when r is
        Ok v -> v
        Err e ->
            dbg
                e

            crash "orCrash encounted Err"
