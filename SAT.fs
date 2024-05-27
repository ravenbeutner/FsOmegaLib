(*    
    Copyright (C) 2022-2024 Raven Beutner

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
*)

module FsOmegaLib.SAT

open System.Collections.Generic

type Literal<'T> =
    | PL of 'T
    | NL of 'T

    member this.Value =
        match this with
        | PL x
        | NL x -> x

module Literal =
    let getValue (l : Literal<'T>) = l.Value

    let map f (l : Literal<'T>) =
        match l with
        | PL x -> PL(f x)
        | NL x -> NL(f x)

    let isConjunctionSat (c : list<Literal<'T>>) =
        let d = new Dictionary<_, _>()

        let mutable br = false
        let mutable i = 0
        let mutable isSat = true

        while (not br) && i < c.Length do
            let l = c.[i]

            match l with
            | PL y ->
                if d.ContainsKey y then
                    if d.[y] = false then
                        isSat <- false
                        br <- true
                else
                    d.Add(y, true)
            | NL y ->
                if d.ContainsKey y then
                    if d.[y] = true then
                        isSat <- false
                        br <- true
                else
                    d.Add(y, false)

            i <- i + 1

        isSat

    let simplifyConjunction (c : list<Literal<'T>>) =
        let d = new Dictionary<_, _>()

        let mutable br = false
        let mutable i = 0
        let mutable isSat = Some []

        while (not br) && i < c.Length do
            let l = c.[i]

            match l with
            | PL y ->
                if d.ContainsKey y then
                    if d.[y] = false then
                        isSat <- None
                        br <- true
                else
                    d.Add(y, true)
                    isSat <- isSat |> Option.map (fun x -> (PL y) :: x)
            | NL y ->
                if d.ContainsKey y then
                    if d.[y] = true then
                        isSat <- None
                        br <- true
                else
                    d.Add(y, false)
                    isSat <- isSat |> Option.map (fun x -> (NL y) :: x)

            i <- i + 1

        isSat

type DNF<'T when 'T : comparison> = list<list<Literal<'T>>>

module DNF =
    let isSat (dnf : DNF<'T>) =
        dnf |> List.exists (fun c -> Literal.isConjunctionSat c)

    let simplify (dnf : DNF<'T>) =
        List.choose Literal.simplifyConjunction dnf

    let print (dnf : DNF<'T>) =
        let printConjunct c =
            if List.isEmpty c then
                "t"
            else
                c
                |> List.map (fun l ->
                    match l with
                    | PL x -> string x
                    | NL x -> "!" + string x
                )
                |> List.reduce (fun a b -> a + "&" + b)

        if List.isEmpty dnf then
            "f"
        else
            dnf
            |> List.map (fun x -> "(" + printConjunct x + ")")
            |> List.reduce (fun a b -> a + "|" + b)

    let eval (A : 'T -> bool) (dnf : DNF<'T>) =
        dnf
        |> List.exists (fun c ->
            c
            |> List.forall (fun l ->
                match l with
                | PL x -> A x
                | NL x -> not (A x)
            )
        )

    let map (f : 'T -> 'U) (dnf : DNF<'T>) =
        dnf |> List.map (List.map (fun x -> Literal.map f x))

    let atoms (dnf : DNF<'T>) =
        dnf |> List.map (List.map (fun x -> x.Value)) |> List.concat |> set

    let fixValues (m : Map<'T, bool>) (dnf : DNF<'T>) : DNF<'T> =

        let fixValuesInConjunct c =
            let getsUnsat =
                c
                |> List.exists (fun l ->
                    match l with
                    | PL x -> m.ContainsKey x && not m.[x]
                    | NL x -> m.ContainsKey x && m.[x]
                )

            if getsUnsat then
                None
            else
                c |> List.filter (fun l -> m.ContainsKey l.Value |> not) |> Some

        dnf |> List.choose fixValuesInConjunct

    let fixValuesLazily (m : 'T -> option<bool>) (dnf : DNF<'T>) : DNF<'T> =
        let rec fixValuesInConjunct (c: Literal<'T> list) (acc: Literal<'T> list) =
            match c with 
            | [] -> Some acc 
            | (PL x) :: xs -> 
                match m x with 
                | None -> fixValuesInConjunct xs (PL x :: acc)
                | Some true -> fixValuesInConjunct xs acc 
                | Some false -> None // The clause becomes FALSE
            | (NL x) :: xs -> 
                match m x with 
                | None -> fixValuesInConjunct xs (NL x :: acc)
                | Some false -> fixValuesInConjunct xs acc 
                | Some true -> None // The clause becomes FALSE

        let rec t (dnf) (acc) = 
            match dnf with 
            | [] -> acc 
            | c :: xs -> 
                match fixValuesInConjunct c [] with 
                | None -> 
                    // Conjunct becomes FALSE 
                    t xs acc 
                | Some c' -> 
                    t xs (c' :: acc) 

        t dnf []
        
    let existentialProjection (p : Set<'T>) (dnf : DNF<'T>) =
        let projectConjunct (c : list<Literal<'T>>) =
            c |> List.filter (fun l -> Set.contains l.Value p |> not)

        dnf |> List.map projectConjunct

    let constructConjunction (dnfList : list<DNF<'T>>) =
        dnfList
        |> List.map seq
        |> Util.cartesianProduct
        |> Seq.choose (fun x -> List.concat x |> Literal.simplifyConjunction)
        |> Seq.toList

    let trueDNF : DNF<'T> = [ [] ]

    let falseDNF : DNF<'T> = []

type BooleanExpression<'T when 'T : comparison> =
    | Atom of 'T
    | True
    | False
    | Neg of BooleanExpression<'T>
    | And of list<BooleanExpression<'T>>
    | Or of list<BooleanExpression<'T>>

module BooleanExpression =
    let rec printInHoaFormat (b : BooleanExpression<'T>) =
        match b with
        | Atom x -> string x
        | True -> "t"
        | False -> "f"
        | Neg c -> "(!" + printInHoaFormat c + ")"
        | And l -> "(" + (l |> List.map (fun x -> printInHoaFormat x) |> String.concat "&") + ")"
        | Or l -> "(" + (l |> List.map (fun x -> printInHoaFormat x) |> String.concat "|") + ")"

    let rec eval (A : 'T -> bool) (b : BooleanExpression<'T>) =
        match b with
        | Atom x -> A x
        | True -> true
        | False -> false
        | Neg c -> not (eval A c)
        | And l -> l |> List.forall (fun x -> eval A x)
        | Or l -> l |> List.exists (fun x -> eval A x)

    let rec map (f : 'T -> 'U) (b : BooleanExpression<'T>) =
        match b with
        | Atom x -> Atom(f x)
        | True -> True
        | False -> False
        | Neg c -> Neg(map f c)
        | And l -> l |> List.map (fun x -> map f x) |> And
        | Or l -> l |> List.map (fun (x : BooleanExpression<'T>) -> map f x) |> Or

    let rec atoms (b : BooleanExpression<'T>) =
        match b with
        | Atom x -> Set.singleton x
        | True
        | False -> Set.empty
        | Neg e -> atoms e
        | And l
        | Or l -> l |> List.map (fun x -> atoms x) |> Set.unionMany

    let rec fixValues (m : Map<'T, bool>) (b : BooleanExpression<'T>) =
        match b with
        | Atom x ->
            if m.ContainsKey x then
                (if m.[x] then True else False)
            else
                Atom x
        | True -> True
        | False -> False
        | Neg c -> Neg(fixValues m c)
        | And l -> l |> List.map (fun x -> fixValues m x) |> And
        | Or l -> l |> List.map (fun (x : BooleanExpression<'T>) -> fixValues m x) |> Or

let convertBooleanExpressionToDNF (e : BooleanExpression<'T>) : DNF<'T> =
    let rec recursiveConverter e =
        match e with
        | Atom(x) -> [ [ PL x ] ]
        | True -> [ [] ]
        | False -> []
        | Or l -> l |> List.map recursiveConverter |> List.concat

        | And l ->
            let conjuncts = l |> List.map recursiveConverter |> List.map seq

            Util.cartesianProduct conjuncts |> Seq.map List.concat |> Seq.toList

        | Neg e ->
            match e with
            | Atom x -> [ [ NL x ] ]
            | Neg e' -> recursiveConverter e'
            | True -> recursiveConverter False
            | False -> recursiveConverter True
            | And l -> l |> List.map Neg |> Or |> recursiveConverter
            | Or l -> l |> List.map Neg |> And |> recursiveConverter

    recursiveConverter e

let convertDNFToBooleanExpression (dnf : DNF<'T>) =
    let mappedDisjunction =
        dnf
        |> List.map (fun conjunction ->
            let mappedConjunction =
                conjunction
                |> List.map (fun l ->
                    match l with
                    | PL x -> Atom x
                    | NL x -> Neg(Atom x)
                )

            match mappedConjunction with
            | [] -> BooleanExpression.True
            | [ x ] -> x
            | _ -> And mappedConjunction
        )

    match mappedDisjunction with
    | [] -> BooleanExpression.False
    | [ x ] -> x
    | _ -> Or mappedDisjunction


module Parser =
    open FParsec

    let booleanExpressionParser (atomParser : Parser<'T, unit>) : Parser<BooleanExpression<'T>, unit> =
        let bcParser, bcParserRef = createParserForwardedToRef ()

        let atomParser = atomParser |>> (fun x -> BooleanExpression.Atom x)

        let trueParser = stringReturn "t" BooleanExpression.True

        let falseParser = stringReturn "f" BooleanExpression.False

        let parParser = skipChar '(' >>. bcParser .>> spaces .>> skipChar ')'

        let oppBooleanExpression : OperatorPrecedenceParser<BooleanExpression<'T>, unit, unit> =
            new OperatorPrecedenceParser<BooleanExpression<'T>, unit, unit>()

        let addInfixOperator string precedence associativity f =
            oppBooleanExpression.AddOperator(InfixOperator(string, spaces, precedence, associativity, f))

        let addPrefixOperator string precedence associativity f =
            oppBooleanExpression.AddOperator(PrefixOperator(string, spaces, precedence, associativity, f))

        addInfixOperator "&" 20 Associativity.Left (fun e1 e2 -> BooleanExpression.And [ e1; e2 ])
        addInfixOperator "|" 10 Associativity.Left (fun e1 e2 -> BooleanExpression.Or [ e1; e2 ])

        addPrefixOperator "!" 30 true (fun x -> BooleanExpression.Neg x)

        let basicParser =
            spaces >>. choice [ parParser; atomParser; trueParser; falseParser ] .>> spaces

        oppBooleanExpression.TermParser <- basicParser

        do bcParserRef.Value <- oppBooleanExpression.ExpressionParser

        bcParser


    let dnfParser (atomParser : Parser<'T, unit>) : Parser<DNF<'T>, unit> =
        let trueParser = stringReturn "t" DNF.trueDNF

        let falseParser = stringReturn "f" DNF.falseDNF

        let literalParser =
            (skipChar '!' >>. spaces >>. atomParser |>> NL) <|> (atomParser |>> PL)


        let conjunctionParser = sepBy (literalParser .>> spaces) (skipChar '&' .>> spaces)

        let disjunctionParser =
            sepBy (conjunctionParser .>> spaces) (skipChar '|' .>> spaces)

        choice [ trueParser; falseParser; disjunctionParser ]
