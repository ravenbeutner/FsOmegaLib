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

module FsOmegaLib.LTL

open System

type LTL<'T when 'T : comparison> =
    | Atom of 'T
    | True
    | False
    | And of LTL<'T> * LTL<'T>
    | Or of LTL<'T> * LTL<'T>
    | Implies of LTL<'T> * LTL<'T>
    | Equiv of LTL<'T> * LTL<'T>
    | Xor of LTL<'T> * LTL<'T>
    | Not of LTL<'T>
    | X of LTL<'T>
    | F of LTL<'T>
    | G of LTL<'T>
    | U of LTL<'T> * LTL<'T>
    | W of LTL<'T> * LTL<'T>
    | M of LTL<'T> * LTL<'T>
    | R of LTL<'T> * LTL<'T>

module LTL =

    let rec printInSpotFormat (varNames : 'T -> String) (formula : LTL<'T>) =
        match formula with
        | Atom x -> varNames x
        | True -> "1"
        | False -> "0"
        | And(e1, e2) ->
            "("
            + printInSpotFormat varNames e1
            + " & "
            + printInSpotFormat varNames e2
            + ")"
        | Or(e1, e2) ->
            "("
            + printInSpotFormat varNames e1
            + " | "
            + printInSpotFormat varNames e2
            + ")"
        | Implies(e1, e2) ->
            "("
            + printInSpotFormat varNames e1
            + " -> "
            + printInSpotFormat varNames e2
            + ")"
        | Equiv(e1, e2) ->
            "("
            + printInSpotFormat varNames e1
            + " <-> "
            + printInSpotFormat varNames e2
            + ")"
        | Xor(e1, e2) ->
            "("
            + printInSpotFormat varNames e1
            + " xor "
            + printInSpotFormat varNames e2
            + ")"
        | Not e -> "(! " + printInSpotFormat varNames e + ")"
        | X e -> "(X " + printInSpotFormat varNames e + ")"
        | F e -> "(F " + printInSpotFormat varNames e + ")"
        | G e -> "(G " + printInSpotFormat varNames e + ")"
        | U(e1, e2) ->
            "("
            + printInSpotFormat varNames e1
            + " U "
            + printInSpotFormat varNames e2
            + ")"
        | W(e1, e2) ->
            "("
            + printInSpotFormat varNames e1
            + " W "
            + printInSpotFormat varNames e2
            + ")"
        | M(e1, e2) ->
            "("
            + printInSpotFormat varNames e1
            + " M "
            + printInSpotFormat varNames e2
            + ")"
        | R(e1, e2) ->
            "("
            + printInSpotFormat varNames e1
            + " R "
            + printInSpotFormat varNames e2
            + ")"

    let rec map (f : 'T -> 'U) (formula : LTL<'T>) =
        match formula with
        | Atom x -> Atom(f x)
        | True -> True
        | False -> False
        | And(e1, e2) -> And(map f e1, map f e2)
        | Implies(e1, e2) -> Implies(map f e1, map f e2)
        | Equiv(e1, e2) -> Equiv(map f e1, map f e2)
        | Xor(e1, e2) -> Xor(map f e1, map f e2)
        | Or(e1, e2) -> Or(map f e1, map f e2)
        | U(e1, e2) -> U(map f e1, map f e2)
        | W(e1, e2) -> W(map f e1, map f e2)
        | M(e1, e2) -> M(map f e1, map f e2)
        | R(e1, e2) -> R(map f e1, map f e2)
        | F e -> F(map f e)
        | G e -> G(map f e)
        | X e -> X(map f e)
        | Not e -> Not(map f e)

    let rec bind (f : 'T -> LTL<'U>) (formula : LTL<'T>) =
        match formula with
        | Atom x -> f x
        | True -> True
        | False -> False
        | And(e1, e2) -> And(bind f e1, bind f e2)
        | Implies(e1, e2) -> Implies(bind f e1, bind f e2)
        | Equiv(e1, e2) -> Equiv(bind f e1, bind f e2)
        | Xor(e1, e2) -> Xor(bind f e1, bind f e2)
        | Or(e1, e2) -> Or(bind f e1, bind f e2)
        | U(e1, e2) -> U(bind f e1, bind f e2)
        | W(e1, e2) -> W(bind f e1, bind f e2)
        | M(e1, e2) -> M(bind f e1, bind f e2)
        | R(e1, e2) -> R(bind f e1, bind f e2)
        | F e -> F(bind f e)
        | G e -> G(bind f e)
        | X e -> X(bind f e)
        | Not e -> Not(bind f e)

    let rec allAtoms (formula : LTL<'T>) =
        match formula with
        | Atom x -> Set.singleton x
        | True
        | False -> Set.empty
        | And(e1, e2)
        | Implies(e1, e2)
        | Equiv(e1, e2)
        | Xor(e1, e2)
        | Or(e1, e2)
        | U(e1, e2)
        | W(e1, e2)
        | M(e1, e2)
        | R(e1, e2) -> Set.union (allAtoms e1) (allAtoms e2)
        | F e
        | G e
        | X e
        | Not e -> allAtoms e

    let rec size (formula : LTL<'T>) =
        match formula with
        | Atom _
        | True
        | False -> 1
        | And(e1, e2)
        | Implies(e1, e2)
        | Equiv(e1, e2)
        | Xor(e1, e2)
        | Or(e1, e2)
        | U(e1, e2)
        | W(e1, e2)
        | M(e1, e2)
        | R(e1, e2) -> (size e1) + (size e2) + 1
        | F e
        | G e
        | X e
        | Not e -> (size e) + 1

    let rec allSubformulas (formula : LTL<'T>) =
        let subFormulas =
            match formula with
            | Atom _
            | True
            | False -> Set.empty
            | And(e1, e2)
            | Implies(e1, e2)
            | Equiv(e1, e2)
            | Xor(e1, e2)
            | Or(e1, e2)
            | U(e1, e2)
            | W(e1, e2)
            | M(e1, e2)
            | R(e1, e2) -> Set.union (allSubformulas e1) (allSubformulas e2)
            | F e
            | G e
            | X e
            | Not e -> allSubformulas e

        Set.add formula subFormulas


module Parser =
    open FParsec

    let ltlParser (atomParser : Parser<'T, unit>) =
        let ltlParser, ltlParserRef = createParserForwardedToRef ()

        let trueParser = stringReturn "1" True <|> stringReturn "true" True

        let falseParser = stringReturn "0" False <|> stringReturn "false" False

        let variableParser = atomParser |>> Atom

        let parParser = skipChar '(' >>. spaces >>. ltlParser .>> spaces .>> skipChar ')'


        let basicParser =
            spaces >>. choice [ trueParser; falseParser; variableParser; parParser ]
            .>> spaces

        let oppLtl = new OperatorPrecedenceParser<LTL<'T>, unit, unit>()

        let addInfixOperator string precedence associativity f =
            oppLtl.AddOperator(InfixOperator(string, spaces, precedence, associativity, f))

        let addPrefixOperator string precedence associativity f =
            oppLtl.AddOperator(PrefixOperator(string, spaces, precedence, associativity, f))

        do
            oppLtl.TermParser <- basicParser

            addInfixOperator "&" 5 Associativity.Left (fun x y -> And(x, y))
            addInfixOperator "|" 4 Associativity.Left (fun x y -> Or(x, y))
            addInfixOperator "->" 3 Associativity.Left (fun x y -> Implies(x, y))
            addInfixOperator "<->" 2 Associativity.None (fun x y -> Equiv(x, y))
            addInfixOperator "xor" 2 Associativity.None (fun x y -> Xor(x, y))
            addInfixOperator "U" 10 Associativity.Left (fun x y -> U(x, y))
            addInfixOperator "W" 10 Associativity.Left (fun x y -> W(x, y))
            addInfixOperator "M" 10 Associativity.Left (fun x y -> M(x, y))
            addInfixOperator "R" 10 Associativity.Left (fun x y -> R(x, y))

            addPrefixOperator "F" 20 true (fun x -> F x)
            addPrefixOperator "G" 20 false (fun x -> G x)
            addPrefixOperator "X" 30 true (fun x -> X x)
            addPrefixOperator "!" 40 true (fun x -> Not x)

        do ltlParserRef.Value <- oppLtl.ExpressionParser

        ltlParser

    let parseLTL (atomParser : Parser<'T, unit>) s =
        let full = ltlParser atomParser .>> spaces .>> eof
        let res = run full s

        match res with
        | Success(res, _, _) -> Result.Ok res
        | Failure(err, _, _) -> Result.Error err
