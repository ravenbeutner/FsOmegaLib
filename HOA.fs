(*    
    Copyright (C) 2022-2023 Raven Beutner

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

module internal FsOmegaLib.HOA   

open System 

open SAT

type AcceptanceSetAtom =
    | PosAcceptanceSet of int 
    | NegAcceptanceSet of int 

type AcceptanceCondition = 
    | AccAtomFin of AcceptanceSetAtom
    | AccAtomInf of AcceptanceSetAtom
    | AccTrue 
    | AccFalse 
    | AccAnd of AcceptanceCondition * AcceptanceCondition
    | AccOr of AcceptanceCondition * AcceptanceCondition

type AutomatonHeader = 
    {
        HoaVersion : option<string>
        States : option<int>
        Start : list<int>
        APs : option<list<String>>
        Properties : list<String> 
        Tool : option<list<String>>
        Name : option<String>
        Acceptance : option<int * AcceptanceCondition>
        AcceptanceName : option<String>
    }

type AutomatonBody = 
    {
        StateMap : Map<int, Set<int> * list<DNF<int> * int>>
    }

type HoaAutomaton = 
    {
        Header : AutomatonHeader;
        Body : AutomatonBody
    }

module Parser =
    open FParsec
    
    
    let rec private multilineCommentParser =
        let openMultilineCommentStr = "/*"
        let closeMultilineCommentStr = "*/"
        between
            (pstring openMultilineCommentStr)
            (pstring closeMultilineCommentStr)
            (charsTillString closeMultilineCommentStr false System.Int32.MaxValue)
        |>> ignore
    
    let private spacesNoNewline = manyChars (satisfy (fun x -> x = ' ' || x = '\t')) |>> ignore

    let private ws =
        spaces >>. many (multilineCommentParser .>> spaces)
        |>> ignore


    let private wsNoNewline =
        spacesNoNewline >>. many (multilineCommentParser .>> spacesNoNewline)
        |>> ignore
    
    let private headerParser =
        let headerLineParser (header : AutomatonHeader) = 

            let hoaParser = 
                skipString "HOA:" >>. wsNoNewline >>. many1Chars (satisfy (fun x -> x <> ' ' && x <> '\n'))
                |>> (fun x -> {header with HoaVersion = Some x})

            let nameParser  = 
                let escapedStringParser = 
                    skipChar '\"' >>. many1Chars (satisfy (fun c -> c <> '\"')) .>> skipChar '\"'

                skipString "name:" >>. wsNoNewline >>. escapedStringParser
                |>> fun x -> {header with Name = Some x}

            let toolParser  = 
                let escapedStringParser = 
                    skipChar '\"' >>. many1Chars (satisfy (fun c -> c <> '\"')) .>> skipChar '\"'

                skipString "tool:" >>. wsNoNewline >>. many1 (escapedStringParser .>> wsNoNewline)
                |>> fun x -> {header with Tool = Some x}


            let apParser  = 
                let escapedStringParser = 
                    skipChar '\"' >>. many1Chars (satisfy (fun c -> c <> '\"')) .>> skipChar '\"'

                skipString "AP:" >>. wsNoNewline >>.
                    pipe2 
                        pint32 
                        (wsNoNewline >>. many (escapedStringParser .>> wsNoNewline))
                        (fun _ y -> {header with APs = Some y})

            let statesParser  = 
                skipString "States:" >>. wsNoNewline >>. pint32
                |>> fun x -> {header with States = Some x}

            let startParser = 
                skipString "Start:" >>. wsNoNewline >>. pint32
                |>> fun x -> {header with Start = x::header.Start}


            let propertiesParser = 
                skipString "properties:" >>. wsNoNewline >>. many1 (many1Chars (satisfy (fun x -> x <> ' ' && x <> '\n')) .>> wsNoNewline)
                |>> fun x -> {header with Properties = x @ header.Properties}
                

            let accNameParser = 
                skipString "acc-name:" >>. wsNoNewline >>. many1 (many1Chars (satisfy (fun x -> x <> ' ' && x <> '\n')) .>> wsNoNewline)
                |>> fun x -> {header with AcceptanceName = Util.combineStringsWithSeperator " " x |> Some}

            let accParser = 
                let accParser, accParserRef = createParserForwardedToRef()

                let literalParser = 
                    (skipChar '!' >>. wsNoNewline >>. pint32 |>> AcceptanceSetAtom.NegAcceptanceSet)
                    <|>
                    (pint32 |>> AcceptanceSetAtom.PosAcceptanceSet)

                let infParser = 
                    skipString "Inf" >>. wsNoNewline .>> skipChar '(' >>. wsNoNewline >>. literalParser .>> wsNoNewline .>> pchar ')'
                    |>> AccAtomInf

                let finParser = 
                    skipString "Fin" >>. wsNoNewline .>> skipChar '(' >>. wsNoNewline >>. literalParser .>> wsNoNewline .>> pchar ')'
                    |>> AccAtomFin

                let parParser = 
                    skipChar '(' >>. accParser .>> wsNoNewline .>> skipChar ')'

                let falseParser = 
                    charReturn 'f' AccFalse

                let trueParser = 
                    charReturn 't' AccTrue
                
                let opp = new OperatorPrecedenceParser<AcceptanceCondition, unit, unit>()
                
                let addInfixOperator str precedence associativity f =
                    opp.AddOperator(
                        InfixOperator(str, wsNoNewline, precedence, associativity, f)
                    )

                addInfixOperator "&" 20 Associativity.Left (fun e1 e2 -> AccAnd(e1, e2))
                addInfixOperator "|" 10 Associativity.Left (fun e1 e2 -> AccOr(e1, e2))

                let innerParser = 
                    wsNoNewline >>. choice [
                        falseParser
                        trueParser
                        infParser
                        finParser
                        parParser
                    ] .>> wsNoNewline

                opp.TermParser <- innerParser
                
                do accParserRef.Value <- opp.ExpressionParser

                skipString "Acceptance:" >>. wsNoNewline >>. pint32 .>>. accParser
                |>> fun (x, y) -> {header with Acceptance = Some (x, y)}

            choice [
                hoaParser
                nameParser
                toolParser
                apParser
                statesParser
                startParser
                propertiesParser
                accNameParser
                accParser
            ] .>> ws

        let initHeader = 
            {
                HoaVersion = None
                States = None
                Start = []
                APs = None
                Properties  = []
                Tool  = None
                Name = None
                Acceptance  = None
                AcceptanceName = None
            }
        
        let rec headerParserRec (header: AutomatonHeader) =
            (attempt (headerLineParser header) >>= headerParserRec)
            <|>% header
        
        headerParserRec initHeader
        
    let private bodyParser =
        let edgeParser = 
            let guardParser = 
                pchar '[' >>. ws >>. 
                choice [
                    (attempt (SAT.Parser.dnfParser pint32));
                    (SAT.Parser.booleanExpressionParser pint32 |>> fun x -> SAT.convertBooleanExpressionToDNF x)
                ]
                .>> ws .>> pchar ']'

            pipe2 
                guardParser
                (ws >>. pint32)
                (fun g t -> g, t)

        let stateParser = 
            let stateHeadParser = 
                pstring "State:" >>.
                    pipe2 
                        (ws >>. pint32 .>> ws)
                        (
                            (between (skipChar '{' .>> ws) (skipChar '}') (many (pint32 .>> ws)) |>> fun x -> set x)
                            <|>
                            (preturn Set.empty)
                        )
                        (fun a b -> (a, b))

            pipe2 
                (stateHeadParser .>> ws)
                (many (edgeParser .>> ws))
                (fun (id, c) y -> id, c, y)

        ws >>. many (stateParser .>> ws)
        |>> fun x -> 
            x 
            |> List.map (fun (x, y, z) -> (x, (y, z)))
            |> Map.ofList
            |> fun x -> {AutomatonBody.StateMap = x}

    let private hoaParser =
        pipe3 
            headerParser
            (ws .>> skipString "--BODY--" .>> ws)
            (bodyParser .>> ws .>> skipString "--END--" .>> ws .>> eof)
            (fun x _ y -> {HoaAutomaton.Header = x; Body = y})

    let parseHoaAutomaton (s: string) =
        let res = run hoaParser s
        match res with
        | Success (res, _, _) -> Result.Ok res
        | Failure (err, _, _) -> Result.Error err

