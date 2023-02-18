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
    
    let rec private multilineCommentParser o=
        let ign x = charsTillString x false System.Int32.MaxValue |>> ignore
        let openMultilineCommentStr = "/*"
        let closeMultilineCommentStr = "*/"
        (between
            (pstring openMultilineCommentStr)
            (pstring closeMultilineCommentStr)
            (attempt (ign openMultilineCommentStr >>. multilineCommentParser >>. ign closeMultilineCommentStr) <|> 
            ign closeMultilineCommentStr) <|o)

    let private whitespace =
        multilineCommentParser <|>
        spaces

    let private ws = skipMany whitespace
    
    let private headerParser =
        let headerLineParser (header : AutomatonHeader) = 

            let hoaParser = 
                skipString "HOA:" >>. ws >>. many1Chars (satisfy (fun x -> x <> ' ' && x <> '\n'))
                |>> (fun x -> {header with HoaVersion = Some x})

            let nameParser  = 
                let escapedStringParser = 
                    skipChar '\"' >>. many1Chars (satisfy (fun c -> c <> '\"')) .>> skipChar '\"'

                skipString "name:" >>. ws >>. escapedStringParser
                |>> fun x -> {header with Name = Some x}

            let toolParser  = 
                let escapedStringParser = 
                    skipChar '\"' >>. many1Chars (satisfy (fun c -> c <> '\"')) .>> skipChar '\"'

                skipString "tool:" >>. ws >>. many1 (escapedStringParser .>> ws)
                |>> fun x -> {header with Tool = Some x}


            let apParser  = 
                let escapedStringParser = 
                    skipChar '\"' >>. many1Chars (satisfy (fun c -> c <> '\"')) .>> skipChar '\"'

                skipString "AP:" >>. ws >>.
                    pipe2 
                        pint32 
                        (ws >>. many (escapedStringParser .>> ws))
                        (fun _ y -> {header with APs = Some y})

            let statesParser  = 
                skipString "States:" >>. ws >>. pint32
                |>> fun x -> {header with States = Some x}

            let startParser = 
                skipString "Start:" >>. ws >>. pint32
                |>> fun x -> {header with Start = x::header.Start}


            let propertiesParser = 
                skipString "properties:" >>. ws >>. many1 (many1Chars (satisfy (fun x -> x <> ' ' && x <> '\n')) .>> ws)
                |>> fun x -> {header with Properties = x @ header.Properties}
                

            let accNameParser = 
                skipString "acc-name:" >>. ws >>. many1 (many1Chars (satisfy (fun x -> x <> ' ' && x <> '\n')) .>> ws)
                |>> fun x -> {header with AcceptanceName = Util.combineStringsWithSeperator " " x |> Some}

            let accParser = 
                let accParser, accParserRef = createParserForwardedToRef()

                let literalParser = 
                    (skipChar '!' >>. ws >>. pint32 |>> AcceptanceSetAtom.NegAcceptanceSet)
                    <|>
                    (pint32 |>> AcceptanceSetAtom.PosAcceptanceSet)

                let infParser = 
                    skipString "Inf" >>. ws .>> skipChar '(' >>. ws >>. literalParser .>> ws .>> pchar ')'
                    |>> AccAtomInf

                let finParser = 
                    skipString "Fin" >>. ws .>> skipChar '(' >>. ws >>. literalParser .>> ws .>> pchar ')'
                    |>> AccAtomFin

                let parParser = 
                    skipChar '(' >>. accParser .>> ws .>> skipChar ')'

                let falseParser = 
                    charReturn 'f' AccFalse

                let trueParser = 
                    charReturn 't' AccTrue
                
                let opp = new OperatorPrecedenceParser<AcceptanceCondition, unit, unit>()
                
                let addInfixOperator str precedence associativity f =
                    opp.AddOperator(
                        InfixOperator(str, ws, precedence, associativity, f)
                    )

                addInfixOperator "&" 20 Associativity.Left (fun e1 e2 -> AccAnd(e1, e2))
                addInfixOperator "|" 10 Associativity.Left (fun e1 e2 -> AccOr(e1, e2))

                let innerParser = 
                    ws >>. choice [
                        falseParser
                        trueParser
                        infParser
                        finParser
                        parParser
                    ] .>> ws

                opp.TermParser <- innerParser
                
                do accParserRef.Value <- opp.ExpressionParser

                skipString "Acceptance:" >>. ws >>. pint32 .>>. accParser
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
                (attempt (SAT.Parser.dnfParser pint32)) <|> (SAT.Parser.booleanExpressionParser pint32 |>> fun x -> SAT.convertBooleanExpressionToDNF x)
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

