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

module FsOmegaLib.Operations

open System.IO

open Util.SubprocessUtil
open HOA
open AbstractAutomaton
open AutomatonSkeleton
open GNBA
open NBA
open DPA
open NPA
open NSA
open APA
open LTL

type FsOmegaLibError =
    {
        Info : string // A user-friendly error message that should be displayed to the user
        DebugInfo : string
    } // Additional Information that can be used for debugging

type AutomataOperationResult<'T> =
    | Success of 'T
    | Fail of FsOmegaLibError

module AutomataOperationResult =
    let defaultValue (value : 'T) (result : AutomataOperationResult<'T>) =
        match result with
        | Success x -> x
        | Fail _ -> value

    let defaultWith (defThunk : FsOmegaLibError -> 'T) (result : AutomataOperationResult<'T>) =
        match result with
        | Success x -> x
        | Fail err -> defThunk err


exception internal ConversionException of FsOmegaLibError

type Effort =
    | LOW
    | MEDIUM
    | HIGH

module Effort =
    let asString (ef : Effort) =
        match ef with
        | LOW -> "low"
        | MEDIUM -> "medium"
        | HIGH -> "high"


module private HoaConversion =

    let private extractAlternatingSkeletonFromHoa (hoaAut : HoaAutomaton) =
        let header = hoaAut.Header
        let body = hoaAut.Body

        {
            AutomatonSkeleton.States = body.StateMap.Keys |> set
            APs = header.APs
            Edges = body.StateMap |> Map.toSeq |> Seq.map (fun (k, (_, e)) -> k, e) |> Map.ofSeq
        }

    let private extractNondeterministicSkeletonFromHoa (hoaAut : HoaAutomaton) =
        hoaAut
        |> extractAlternatingSkeletonFromHoa
        |> NondeterministicAutomatonSkeleton.tryFromAlternatingAutomatonSkeleton
        |> Option.defaultWith (fun _ ->
            raise
            <| ConversionException
                {
                    Info = $"Could not convert HANOI automaton"
                    DebugInfo = $"Could not convert HANOI automaton; The HANOI automaton has universal branching"
                }
        )


    let convertHoaToGNBA (hoaAut : HoaAutomaton) =
        let header = hoaAut.Header
        let body = hoaAut.Body

        let rec isGNBAAccCondition (cond : AcceptanceCondition) =
            match cond with
            | AccAtomFin _ -> false
            | AccAtomInf(PosAcceptanceSet _) -> true
            | AccAtomInf(NegAcceptanceSet _) -> false
            | AccTrue -> true
            | AccFalse -> false
            | AccAnd(l1, l2) -> isGNBAAccCondition l1 && isGNBAAccCondition l2
            | AccOr _ -> false

        let numberOfAccSets, acc = header.Acceptance

        if isGNBAAccCondition acc |> not then
            raise
            <| ConversionException
                {
                    Info = $"Could not convert HANOI automaton to GNBA"
                    DebugInfo =
                        $"Could not convert HANOI automaton to GNBA; No valid Acceptance condition for a GNBA: %A{header.Acceptance}"
                }

        {
            GNBA.Skeleton = extractNondeterministicSkeletonFromHoa hoaAut
            InitialStates =
                header.Start
                |> List.map (
                    function
                    | [ x ] -> x
                    | _ ->
                        raise
                        <| ConversionException
                            {
                                Info = $"Could not convert HANOI automaton to GNBA"
                                DebugInfo =
                                    $"Could not convert HANOI automaton to GNBA; The HANOI automaton uses conjunctions of initial states"
                            }
                )
                |> set
            AcceptanceSets = body.StateMap |> Map.toSeq |> Seq.map (fun (k, (a, _)) -> k, a) |> Map.ofSeq
            NumberOfAcceptingSets = numberOfAccSets
        }

    let convertHoaToNBA (hoaAut : HoaAutomaton) =
        let body = hoaAut.Body

        if hoaAut.Header.Acceptance <> (1, AccAtomInf(PosAcceptanceSet 0)) then
            raise
            <| ConversionException
                {
                    Info = $"Could not convert HANOI automaton to NBA"
                    DebugInfo =
                        $"Could not convert HANOI automaton to NBA; No valid Acceptance condition for a NBA: %A{hoaAut.Header.Acceptance}"
                }

        {
            NBA.Skeleton = extractNondeterministicSkeletonFromHoa hoaAut
            InitialStates =
                hoaAut.Header.Start
                |> List.map (
                    function
                    | [ x ] -> x
                    | _ ->
                        raise
                        <| ConversionException
                            {
                                Info = $"Could not convert HANOI automaton to NBA"
                                DebugInfo =
                                    $"Could not convert HANOI automaton to NBA; The HANOI automaton uses conjunctions of initial states"
                            }
                )
                |> set
            AcceptingStates =
                body.StateMap
                |> Map.toSeq
                |> Seq.filter (fun (_, (a, _)) -> Set.contains 0 a)
                |> Seq.map fst
                |> set
        }

    let convertHoaToNSA (hoaAut : HoaAutomaton) =
        match hoaAut.Header.Acceptance with
        | 0, AccTrue -> ()
        | _ ->
            raise
            <| ConversionException
                {
                    Info = $"Could not convert HANOI automaton to NSA"
                    DebugInfo = $"Could not convert HANOI automaton to NSA"
                }

        {
            NSA.Skeleton = extractNondeterministicSkeletonFromHoa hoaAut
            InitialStates =
                hoaAut.Header.Start
                |> List.map (
                    function
                    | [ x ] -> x
                    | _ ->
                        raise
                        <| ConversionException
                            {
                                Info = $"Could not convert HANOI automaton to NSA"
                                DebugInfo =
                                    $"Could not convert HANOI automaton to NSA; The HANOI automaton uses conjunctions of initial states"
                            }
                )
                |> set
        }

    let convertHoaToDPA (hoaAut : HoaAutomaton) =
        let body = hoaAut.Body

        // Check that the acc condition is a max-even condition
        let rec isParityCondition (_ : AcceptanceCondition) =
            // TODO, check for parity acceptance
            true

        let _, acc = hoaAut.Header.Acceptance

        if isParityCondition acc |> not then
            raise
            <| ConversionException
                {
                    Info = $"Could not convert HANOI automaton to DPA"
                    DebugInfo =
                        $"Could not convert HANOI automaton to DPA; No valid Acceptance condition for a parity automaton: %A{hoaAut.Header.Acceptance}"
                }

        {
            DPA.Skeleton = extractNondeterministicSkeletonFromHoa hoaAut
            InitialState =
                match hoaAut.Header.Start with
                | [ [ x ] ] -> x
                | _ ->
                    raise
                    <| ConversionException
                        {
                            Info = $"Could not convert HANOI automaton to DPA"
                            DebugInfo =
                                $"Could not convert HANOI automaton to DPA; The HOA automaton does not define a unique initial state"
                        }
            Color = body.StateMap |> Map.map (fun _ x -> x |> fst |> Set.toList |> List.head)
        }

    let convertHoaToNPA (hoaAut : HoaAutomaton) =
        let body = hoaAut.Body

        // Check that the acc condition is a max-even condition
        let rec isParityCondition (_ : AcceptanceCondition) = true

        let _, acc = hoaAut.Header.Acceptance

        if isParityCondition acc |> not then
            raise
            <| ConversionException
                {
                    Info = $"Could not convert HANOI automaton to NPA"
                    DebugInfo =
                        $"Could not convert HANOI automaton to NPA; No valid Acceptance condition for a parity automaton: %A{hoaAut.Header.Acceptance}"
                }

        {
            NPA.Skeleton = extractNondeterministicSkeletonFromHoa hoaAut
            InitialStates =
                hoaAut.Header.Start
                |> List.map (
                    function
                    | [ x ] -> x
                    | _ ->
                        raise
                        <| ConversionException
                            {
                                Info = $"Could not convert HANOI automaton to NPA"
                                DebugInfo =
                                    $"Could not convert HANOI automaton to NPA; The HANOI automaton uses conjunctions of initial states"
                            }
                )
                |> set
            Color = body.StateMap |> Map.map (fun _ x -> x |> fst |> Set.toList |> List.head)
        }

    let convertHoaToAPA (hoaAut : HoaAutomaton) =
        let body = hoaAut.Body

        // Check that the acc condition is a max-even condition
        let rec isParityCondition (_ : AcceptanceCondition) = true

        let _, acc = hoaAut.Header.Acceptance

        if isParityCondition acc |> not then
            raise
            <| ConversionException
                {
                    Info = $"Could not convert HANOI automaton to APA"
                    DebugInfo =
                        $"Could not convert HANOI automaton to APA; No valid Acceptance condition for a parity automaton: %A{hoaAut.Header.Acceptance}"
                }

        {
            APA.Skeleton = extractAlternatingSkeletonFromHoa hoaAut
            InitialStates = hoaAut.Header.Start |> List.map set |> set
            Color = body.StateMap |> Map.map (fun _ x -> x |> fst |> Set.toList |> List.head)
        }

    let resultToGNBA (res : string) =
        match HOA.Parser.parseHoaAutomaton res with
        | Ok hoa -> convertHoaToGNBA hoa
        | Error err ->
            raise
            <| ConversionException
                {
                    Info = $"Could not parse HANOI automaton"
                    DebugInfo = $"Could not parse HANOI automaton into GNBA: %s{err}"
                }

    let resultToNBA (res : string) =
        match HOA.Parser.parseHoaAutomaton res with
        | Ok hoa -> convertHoaToNBA hoa
        | Error err ->
            raise
            <| ConversionException
                {
                    Info = $"Could not parse HANOI automaton"
                    DebugInfo = $"Could not parse HANOI automaton into NBA: %s{err}"
                }

    let resultToDPA (res : string) =
        match HOA.Parser.parseHoaAutomaton res with
        | Ok hoa -> convertHoaToDPA hoa
        | Error err ->
            raise
            <| ConversionException
                {
                    Info = $"Could not parse HANOI automaton"
                    DebugInfo = $"Could not parse HANOI automaton into DPA: %s{err}"
                }

    let resultToNSA (res : string) =
        match HOA.Parser.parseHoaAutomaton res with
        | Ok hoa -> convertHoaToNSA hoa
        | Error err ->
            raise
            <| ConversionException
                {
                    Info = $"Could not parse HANOI automaton"
                    DebugInfo = $"Could not parse HANOI automaton into NSA: %s{err}"
                }

    let resultToNPA (res : string) =
        match HOA.Parser.parseHoaAutomaton res with
        | Ok hoa -> convertHoaToNPA hoa
        | Error err ->
            raise
            <| ConversionException
                {
                    Info = $"Could not parse HANOI automaton"
                    DebugInfo = $"Could not parse HANOI automaton into NPA: %s{err}"
                }

    let resultToAPA (res : string) =
        match HOA.Parser.parseHoaAutomaton res with
        | Ok hoa -> convertHoaToAPA hoa
        | Error err ->
            raise
            <| ConversionException
                {
                    Info = $"Could not parse HANOI automaton"
                    DebugInfo = $"Could not parse HANOI automaton into APA: %s{err}"
                }


module AutomataUtil =
    let operateHoaAndParse
        (debug : bool)
        (intermediateFilesPath : string)
        (autfiltPath : string)
        (args : string)
        (outputputParser : string -> 'L)
        (hoaString : string)
        =
        try
            let path = Path.Combine [| intermediateFilesPath; "aut1.hoa" |]
            let targetPath = Path.Combine [| intermediateFilesPath; "autRes.hoa" |]

            File.WriteAllText(path, hoaString)

            let arg = args + " " + path + " -o " + targetPath

            let res = Util.SubprocessUtil.executeSubprocess Map.empty autfiltPath arg

            match res with
            | { ExitCode = 0; Stderr = "" } -> File.ReadAllText(targetPath) |> outputputParser |> Success
            | { ExitCode = exitCode; Stderr = stderr } ->
                if exitCode <> 0 then
                    raise
                    <| ConversionException
                        {
                            Info = $"Unexpected exit code by spot"
                            DebugInfo = $"Unexpected exit code by spot: %i{exitCode}"
                        }
                else
                    raise
                    <| ConversionException
                        {
                            Info = $"Error by spot"
                            DebugInfo = $"Error by spot: %s{stderr}"
                        }

        with
        | _ when debug -> reraise ()
        | ConversionException err -> Fail err
        | e ->
            Fail
                {
                    Info = $"Unexpected error"
                    DebugInfo = $"Unexpected error: %s{e.Message}"
                }

    let operateHoaAndParsePair
        (debug : bool)
        (intermediateFilesPath : string)
        (autfiltPath : string)
        (args : string)
        (opp : string)
        (outputputParser : string -> 'L)
        (hoaString1 : string)
        (hoaString2 : string)
        =
        try
            let path1 = Path.Combine [| intermediateFilesPath; "aut1.hoa" |]
            let path2 = Path.Combine [| intermediateFilesPath; "aut2.hoa" |]
            let targetPath = Path.Combine [| intermediateFilesPath; "autRes.hoa" |]

            File.WriteAllText(path1, hoaString1)
            File.WriteAllText(path2, hoaString2)

            let arg = args + " " + opp + path2 + " " + path1 + " -o " + targetPath

            let res = Util.SubprocessUtil.executeSubprocess Map.empty autfiltPath arg

            match res with
            | { ExitCode = 0; Stderr = "" } -> File.ReadAllText(targetPath) |> outputputParser |> Success
            | { ExitCode = exitCode; Stderr = stderr } ->
                if exitCode <> 0 then
                    raise
                    <| ConversionException
                        {
                            Info = $"Unexpected exit code by spot"
                            DebugInfo = $"Unexpected exit code by spot: %i{exitCode}"
                        }
                else
                    raise
                    <| ConversionException
                        {
                            Info = $"Error by spot"
                            DebugInfo = $"Error by spot: %s{stderr}"
                        }

        with
        | _ when debug -> reraise ()
        | ConversionException err -> Fail err
        | e ->
            Fail
                {
                    Info = $"Unexpected error"
                    DebugInfo = $"Unexpected error: %s{e.Message}"
                }

    let stringifyAutomaton (aut : AbstractAutomaton<int, 'L>) =
        let dict, revDict =
            aut.Skeleton.APs
            |> List.mapi (fun i x ->
                let a = "l" + string i
                (x, a), (a, x)
            )
            |> List.unzip
            |> fun (x, y) -> Map.ofList x, Map.ofList y

        let s = aut.ToHoaString string (fun x -> dict.[x])

        s, revDict

    let stringifyAutomatonPair (aut1 : AbstractAutomaton<int, 'L>) (aut2 : AbstractAutomaton<int, 'L>) =
        let dict, revDict =
            aut1.Skeleton.APs @ aut2.Skeleton.APs
            |> List.mapi (fun i x ->
                let a = "l" + string i
                (x, a), (a, x)
            )
            |> List.unzip
            |> fun (x, y) -> Map.ofList x, Map.ofList y

        let s1 = aut1.ToHoaString string (fun x -> dict.[x])
        let s2 = aut2.ToHoaString string (fun x -> dict.[x])

        s1, s2, revDict

    let operateHoaToGNBA
        (debug : bool)
        (intermediateFilesPath : string)
        (autfiltPath : string)
        (operations : list<string>)
        (ef : Effort)
        (apRemapping : string -> 'L)
        (hoaString : string)
        =

        let args =
            [ "--small"; "--" + Effort.asString ef; "-S"; "--gba" ] @ operations
            |> String.concat " "

        let hoaOutputputParser c =
            c |> HoaConversion.resultToGNBA |> GNBA.mapAPs apRemapping

        operateHoaAndParse debug intermediateFilesPath autfiltPath args hoaOutputputParser hoaString

    let operateHoaToNBA
        (debug : bool)
        (intermediateFilesPath : string)
        (autfiltPath : string)
        (operations : list<string>)
        (ef : Effort)
        (apRemapping : string -> 'L)
        (hoaString : string)
        =

        let args =
            [ "--small"; "--" + Effort.asString ef; "-S"; "-B" ] @ operations
            |> String.concat " "

        let hoaOutputputParser c =
            c |> HoaConversion.resultToNBA |> NBA.mapAPs apRemapping

        operateHoaAndParse debug intermediateFilesPath autfiltPath args hoaOutputputParser hoaString

    let operateHoaToDPA
        (debug : bool)
        (intermediateFilesPath : string)
        (autfiltPath : string)
        (operations : list<string>)
        (ef : Effort)
        (apRemapping : string -> 'L)
        (hoaString : string)
        =

        let args =
            [ "--small"; "--" + Effort.asString ef; "-D"; "-C"; "-S"; "-p\"max even\"" ]
            @ operations
            |> String.concat " "

        let hoaOutputputParser c =
            c |> HoaConversion.resultToDPA |> DPA.mapAPs apRemapping

        operateHoaAndParse debug intermediateFilesPath autfiltPath args hoaOutputputParser hoaString

    let operateHoaToNPA
        (debug : bool)
        (intermediateFilesPath : string)
        (autfiltPath : string)
        (operations : list<string>)
        (ef : Effort)
        (apRemapping : string -> 'L)
        (hoaString : string)
        =

        let args =
            [ "--small"; "--" + Effort.asString ef; "-S"; "-p\"max even\"" ] @ operations
            |> String.concat " "

        let hoaOutputputParser c =
            c |> HoaConversion.resultToNPA |> NPA.mapAPs apRemapping

        operateHoaAndParse debug intermediateFilesPath autfiltPath args hoaOutputputParser hoaString

    let operateHoaToNSA
        (debug : bool)
        (intermediateFilesPath : string)
        (autfiltPath : string)
        (operations : list<string>)
        (ef : Effort)
        (apRemapping : string -> 'L)
        (hoaString : string)
        =

        let args =
            [ "--small"; "--" + Effort.asString ef; "-M" ] @ operations |> String.concat " "

        let hoaOutputputParser c =
            c |> HoaConversion.resultToNSA |> NSA.mapAPs apRemapping

        operateHoaAndParse debug intermediateFilesPath autfiltPath args hoaOutputputParser hoaString


    // ==================== Operate on pairs of automata ====================

    let operateHoaPairToGNBA
        (debug : bool)
        (intermediateFilesPath : string)
        (autfiltPath : string)
        (operations : list<string>)
        (opp : string)
        (ef : Effort)
        (apRemapping : string -> 'L)
        (hoaString1 : string)
        (hoaString2 : string)
        =

        let args =
            [ "--small"; "--" + Effort.asString ef; "-S"; "--gba" ] @ operations
            |> String.concat " "

        let hoaOutputputParser c =
            c |> HoaConversion.resultToGNBA |> GNBA.mapAPs apRemapping

        operateHoaAndParsePair debug intermediateFilesPath autfiltPath args opp hoaOutputputParser hoaString1 hoaString2

    // ==================== Operate on LTL formulas to  ====================

    let operateLTLAndParse
        (debug : bool)
        (intermediateFilesPath : string)
        (ltl2tgbaPath : string)
        (args : string)
        (outputputParser : string -> 'L)
        (formula : string)
        =
        try
            let targetPath = Path.Combine [| intermediateFilesPath; "autRes.hoa" |]

            let arg = args + " " + $"\"{formula}\"" + " -o " + targetPath

            let res = Util.SubprocessUtil.executeSubprocess Map.empty ltl2tgbaPath arg

            match res with
            | { ExitCode = 0; Stderr = "" } -> File.ReadAllText(targetPath) |> outputputParser |> Success
            | { ExitCode = exitCode; Stderr = stderr } ->
                if exitCode <> 0 then
                    raise
                    <| ConversionException
                        {
                            Info = $"Unexpected exit code by spot"
                            DebugInfo = $"Unexpected exit code by spot: %i{exitCode}"
                        }
                else
                    raise
                    <| ConversionException
                        {
                            Info = $"Error by spot"
                            DebugInfo = $"Error by spot: %s{stderr}"
                        }

        with
        | _ when debug -> reraise ()
        | ConversionException err -> Fail err
        | e ->
            Fail
                {
                    Info = $"Unexpected error"
                    DebugInfo = $"Unexpected error: %s{e.Message}"
                }


module AutomatonFromHoaString =
    let convertHoaStringToGNBA
        (debug : bool)
        (intermediateFilesPath : string)
        (autfiltPath : string)
        (ef : Effort)
        (hoaString : string)
        =

        AutomataUtil.operateHoaToGNBA debug intermediateFilesPath autfiltPath [] ef id hoaString

    let convertHoaStringToNBA
        (debug : bool)
        (intermediateFilesPath : string)
        (autfiltPath : string)
        (ef : Effort)
        (hoaString : string)
        =

        AutomataUtil.operateHoaToNBA debug intermediateFilesPath autfiltPath [] ef id hoaString

    let convertHoaStringToDPA
        (debug : bool)
        (intermediateFilesPath : string)
        (autfiltPath : string)
        (ef : Effort)
        (hoaString : string)
        =

        AutomataUtil.operateHoaToDPA debug intermediateFilesPath autfiltPath [] ef id hoaString

    let convertHoaStringToNPA
        (debug : bool)
        (intermediateFilesPath : string)
        (autfiltPath : string)
        (ef : Effort)
        (hoaString : string)
        =

        AutomataUtil.operateHoaToNPA debug intermediateFilesPath autfiltPath [] ef id hoaString

    let convertHoaStringToNSA
        (debug : bool)
        (intermediateFilesPath : string)
        (autfiltPath : string)
        (ef : Effort)
        (hoaString : string)
        =

        AutomataUtil.operateHoaToNSA debug intermediateFilesPath autfiltPath [] ef id hoaString


module AutomatonConversions =
    let convertToGNBA
        (debug : bool)
        (intermediateFilesPath : string)
        (autfiltPath : string)
        (ef : Effort)
        (aut : AbstractAutomaton<int, 'L>)
        =
        let hoaString, revDict = AutomataUtil.stringifyAutomaton aut
        AutomataUtil.operateHoaToGNBA debug intermediateFilesPath autfiltPath [] ef (fun x -> revDict.[x]) hoaString

    let convertToNBA
        (debug : bool)
        (intermediateFilesPath : string)
        (autfiltPath : string)
        (ef : Effort)
        (aut : AbstractAutomaton<int, 'L>)
        =

        let hoaString, revDict = AutomataUtil.stringifyAutomaton aut
        AutomataUtil.operateHoaToNBA debug intermediateFilesPath autfiltPath [] ef (fun x -> revDict.[x]) hoaString

    let convertToDPA
        (debug : bool)
        (intermediateFilesPath : string)
        (autfiltPath : string)
        (ef : Effort)
        (aut : AbstractAutomaton<int, 'L>)
        =

        let hoaString, revDict = AutomataUtil.stringifyAutomaton aut
        AutomataUtil.operateHoaToDPA debug intermediateFilesPath autfiltPath [] ef (fun x -> revDict.[x]) hoaString


    let convertToNPA
        (debug : bool)
        (intermediateFilesPath : string)
        (autfiltPath : string)
        (ef : Effort)
        (aut : AbstractAutomaton<int, 'L>)
        =

        let hoaString, revDict = AutomataUtil.stringifyAutomaton aut
        AutomataUtil.operateHoaToNPA debug intermediateFilesPath autfiltPath [] ef (fun x -> revDict.[x]) hoaString


    let convertToNSA
        (debug : bool)
        (intermediateFilesPath : string)
        (autfiltPath : string)
        (ef : Effort)
        (aut : AbstractAutomaton<int, 'L>)
        =

        let hoaString, revDict = AutomataUtil.stringifyAutomaton aut
        AutomataUtil.operateHoaToNSA debug intermediateFilesPath autfiltPath [] ef (fun x -> revDict.[x]) hoaString



module AutomataOperations =
    let complementToGNBA
        debug
        (intermediateFilesPath : string)
        (autfiltPath : string)
        (ef : Effort)
        (aut : AbstractAutomaton<int, 'L>)
        =

        let hoaString, revDict = AutomataUtil.stringifyAutomaton aut

        AutomataUtil.operateHoaToGNBA
            debug
            intermediateFilesPath
            autfiltPath
            [ "--complement" ]
            ef
            (fun x -> revDict.[x])
            hoaString


    let complementToNBA
        debug
        (intermediateFilesPath : string)
        (autfiltPath : string)
        (ef : Effort)
        (aut : AbstractAutomaton<int, 'L>)
        =

        let hoaString, revDict = AutomataUtil.stringifyAutomaton aut

        AutomataUtil.operateHoaToNBA
            debug
            intermediateFilesPath
            autfiltPath
            [ "--complement" ]
            ef
            (fun x -> revDict.[x])
            hoaString

    let complementToDPA
        debug
        (intermediateFilesPath : string)
        (autfiltPath : string)
        (ef : Effort)
        (aut : AbstractAutomaton<int, 'L>)
        =

        let hoaString, revDict = AutomataUtil.stringifyAutomaton aut

        AutomataUtil.operateHoaToDPA
            debug
            intermediateFilesPath
            autfiltPath
            [ "--complement" ]
            ef
            (fun x -> revDict.[x])
            hoaString

    let complementToNPA
        debug
        (intermediateFilesPath : string)
        (autfiltPath : string)
        (ef : Effort)
        (aut : AbstractAutomaton<int, 'L>)
        =

        let hoaString, revDict = AutomataUtil.stringifyAutomaton aut

        AutomataUtil.operateHoaToNPA
            debug
            intermediateFilesPath
            autfiltPath
            [ "--complement" ]
            ef
            (fun x -> revDict.[x])
            hoaString

    let complementToNSA
        debug
        (intermediateFilesPath : string)
        (autfiltPath : string)
        (ef : Effort)
        (aut : AbstractAutomaton<int, 'L>)
        =

        let hoaString, revDict = AutomataUtil.stringifyAutomaton aut

        AutomataUtil.operateHoaToNSA
            debug
            intermediateFilesPath
            autfiltPath
            [ "--complement" ]
            ef
            (fun x -> revDict.[x])
            hoaString


    let unionToGNBA
        debug
        (intermediateFilesPath : string)
        (autfiltPath : string)
        (ef : Effort)
        (aut1 : AbstractAutomaton<int, 'L>)
        (aut2 : AbstractAutomaton<int, 'L>)
        =

        let hoaString1, hoaString2, revDict = AutomataUtil.stringifyAutomatonPair aut1 aut2

        AutomataUtil.operateHoaPairToGNBA
            debug
            intermediateFilesPath
            autfiltPath
            []
            "--product-or="
            ef
            (fun x -> revDict.[x])
            hoaString1
            hoaString2


    let intersectToGNBA
        debug
        (intermediateFilesPath : string)
        (autfiltPath : string)
        (ef : Effort)
        (aut1 : AbstractAutomaton<int, 'L>)
        (aut2 : AbstractAutomaton<int, 'L>)
        =

        let hoaString1, hoaString2, revDict = AutomataUtil.stringifyAutomatonPair aut1 aut2

        AutomataUtil.operateHoaPairToGNBA
            debug
            intermediateFilesPath
            autfiltPath
            []
            "--product="
            ef
            (fun x -> revDict.[x])
            hoaString1
            hoaString2


module LTLConversion =

    let private stringifyLTL (ltl : LTL<'L>) =
        let dict, revDict =
            ltl
            |> LTL.allAtoms
            |> Set.toList
            |> List.mapi (fun i x ->
                let a = "l" + string i
                (x, a), (a, x)
            )
            |> List.unzip
            |> fun (x, y) -> Map.ofList x, Map.ofList y

        let s = ltl |> LTL.printInSpotFormat (fun x -> "\"" + dict.[x] + "\"")

        s, revDict

    let convertLTLtoGNBA debug (intermediateFilesPath : string) (ltl2tgbaPath : string) (ltl : LTL<'L>) =
        let s, revDict = stringifyLTL ltl

        let args = [ "-S" ] |> String.concat " "

        let hoaOutputputParser c =
            c |> HoaConversion.resultToGNBA |> GNBA.mapAPs (fun x -> revDict.[x])

        AutomataUtil.operateLTLAndParse debug intermediateFilesPath ltl2tgbaPath args hoaOutputputParser s


    let convertLTLtoNBA debug (intermediateFilesPath : string) (ltl2tgbaPath : string) (ltl : LTL<'L>) =
        let s, revDict = stringifyLTL ltl

        let args = [ "-S"; "-B" ] |> String.concat " "

        let hoaOutputputParser c =
            c |> HoaConversion.resultToNBA |> NBA.mapAPs (fun x -> revDict.[x])

        AutomataUtil.operateLTLAndParse debug intermediateFilesPath ltl2tgbaPath args hoaOutputputParser s



    let convertLTLtoDPA debug (intermediateFilesPath : string) (ltl2tgbaPath : string) (ltl : LTL<'L>) =
        let s, revDict = stringifyLTL ltl

        let args = [ "-S"; "-C"; "-D"; "-p\"max even\"" ] |> String.concat " "

        let hoaOutputputParser c =
            c |> HoaConversion.resultToDPA |> DPA.mapAPs (fun x -> revDict.[x])

        AutomataUtil.operateLTLAndParse debug intermediateFilesPath ltl2tgbaPath args hoaOutputputParser s

    let convertLTLtoNPA debug (intermediateFilesPath : string) (ltl2tgbaPath : string) (ltl : LTL<'L>) =
        let s, revDict = stringifyLTL ltl

        let args = [ "-S"; "-p\"max even\"" ] |> String.concat " "

        let hoaOutputputParser c =
            c |> HoaConversion.resultToNPA |> NPA.mapAPs (fun x -> revDict.[x])

        AutomataUtil.operateLTLAndParse debug intermediateFilesPath ltl2tgbaPath args hoaOutputputParser s


    let convertLTLtoNSA debug (intermediateFilesPath : string) (ltl2tgbaPath : string) (ltl : LTL<'L>) =
        let s, revDict = stringifyLTL ltl

        let args = [ "-M" ] |> String.concat " "

        let hoaOutputputParser c =
            c |> HoaConversion.resultToNSA |> NSA.mapAPs (fun x -> revDict.[x])

        AutomataUtil.operateLTLAndParse debug intermediateFilesPath ltl2tgbaPath args hoaOutputputParser s


module AutomataChecks =
    let isEmpty debug (intermediateFilesPath : string) (autfiltPath : string) (aut : AbstractAutomaton<int, 'L>) =
        try
            let s, _ = AutomataUtil.stringifyAutomaton aut

            let path = Path.Combine [| intermediateFilesPath; "aut1.hoa" |]
            File.WriteAllText(path, s)

            let args = "--is-empty " + path

            let res = Util.SubprocessUtil.executeSubprocess Map.empty autfiltPath args

            match res with
            | {
                  ExitCode = 0
                  Stderr = ""
                  Stdout = c
              }
            | {
                  ExitCode = 1
                  Stderr = ""
                  Stdout = c
              } ->
                if c = "" then false else true
                |> Success
            | { ExitCode = exitCode; Stderr = stderr } ->
                if exitCode <> 0 && exitCode <> 1 then
                    raise
                    <| ConversionException
                        {
                            Info = $"Unexpected exit code by spot"
                            DebugInfo = $"Unexpected exit code by spot: %i{exitCode}"
                        }
                else
                    raise
                    <| ConversionException
                        {
                            Info = $"Error by spot"
                            DebugInfo = $"Error by spot: %s{stderr}"
                        }
        with
        | _ when debug -> reraise ()
        | ConversionException err -> Fail(err)
        | e ->
            Fail
                {
                    Info = $"Unexpected error"
                    DebugInfo = $"Unexpected error: %s{e.Message}"
                }

    let isContained
        debug
        (intermediateFilesPath : string)
        (autfiltPath : string)
        (aut1 : AbstractAutomaton<int, 'L>)
        (aut2 : AbstractAutomaton<int, 'L>)
        =
        try
            let s1, s2, _ = AutomataUtil.stringifyAutomatonPair aut1 aut2

            let path1 = Path.Combine [| intermediateFilesPath; "aut1.hoa" |]
            let path2 = Path.Combine [| intermediateFilesPath; "aut2.hoa" |]

            File.WriteAllText(path1, s1)
            File.WriteAllText(path2, s2)

            let arg = "--included-in=" + path2 + " " + path1
            let res = Util.SubprocessUtil.executeSubprocess Map.empty autfiltPath arg

            match res with
            | {
                  ExitCode = 0
                  Stderr = ""
                  Stdout = c
              }
            | {
                  ExitCode = 1
                  Stderr = ""
                  Stdout = c
              } ->
                if c = "" then false else true
                |> Success
            | { ExitCode = exitCode; Stderr = stderr } ->
                if exitCode <> 0 && exitCode <> 1 then
                    raise
                    <| ConversionException
                        {
                            Info = $"Unexpected exit code by spot"
                            DebugInfo = $"Unexpected exit code by spot: %i{exitCode}"
                        }
                else
                    raise
                    <| ConversionException
                        {
                            Info = $"Error by spot"
                            DebugInfo = $"Error by spot: %s{stderr}"
                        }
        with
        | _ when debug -> reraise ()
        | ConversionException err -> Fail(err)
        | e ->
            Fail
                {
                    Info = $"Unexpected error"
                    DebugInfo = $"Unexpected error: %s{e.Message}"
                }

    /// Check inclusion using spot's FORQ (only possible with spot version 2.12 or later)
    let isContainedForq
        debug
        (intermediateFilesPath : string)
        (autfiltPath : string)
        (aut1 : AbstractAutomaton<int, 'L>)
        (aut2 : AbstractAutomaton<int, 'L>)
        =
        try
            let s1, s2, _ = AutomataUtil.stringifyAutomatonPair aut1 aut2

            let path1 = Path.Combine [| intermediateFilesPath; "aut1.hoa" |]
            let path2 = Path.Combine [| intermediateFilesPath; "aut2.hoa" |]

            File.WriteAllText(path1, s1)
            File.WriteAllText(path2, s2)

            let arg = "--included-in=" + path2 + " " + path1

            let res =
                Util.SubprocessUtil.executeSubprocess
                    ([ "SPOT_CONTAINMENT_CHECK", "forq" ] |> Map.ofList)
                    autfiltPath
                    arg

            match res with
            | {
                  ExitCode = 0
                  Stderr = ""
                  Stdout = c
              }
            | {
                  ExitCode = 1
                  Stderr = ""
                  Stdout = c
              } ->
                if c = "" then false else true
                |> Success
            | { ExitCode = exitCode; Stderr = stderr } ->
                if exitCode <> 0 && exitCode <> 1 then
                    raise
                    <| ConversionException
                        {
                            Info = $"Unexpected exit code by spot"
                            DebugInfo = $"Unexpected exit code by spot: %i{exitCode}"
                        }
                else
                    raise
                    <| ConversionException
                        {
                            Info = $"Error by spot"
                            DebugInfo = $"Error by spot: %s{stderr}"
                        }
        with
        | _ when debug -> reraise ()
        | ConversionException err -> Fail(err)
        | e ->
            Fail
                {
                    Info = $"Unexpected error"
                    DebugInfo = $"Unexpected error: %s{e.Message}"
                }


    let isEquivalent
        debug
        (intermediateFilesPath : string)
        (autfiltPath : string)
        (aut1 : AbstractAutomaton<int, 'L>)
        (aut2 : AbstractAutomaton<int, 'L>)
        =
        try
            let s1, s2, _ = AutomataUtil.stringifyAutomatonPair aut1 aut2

            let path1 = Path.Combine [| intermediateFilesPath; "aut1.hoa" |]
            let path2 = Path.Combine [| intermediateFilesPath; "aut2.hoa" |]

            File.WriteAllText(path1, s1)
            File.WriteAllText(path2, s2)

            let arg = "--equivalent-to=" + path2 + " " + path1
            let res = Util.SubprocessUtil.executeSubprocess Map.empty autfiltPath arg

            match res with
            | {
                  ExitCode = 0
                  Stderr = ""
                  Stdout = c
              }
            | {
                  ExitCode = 1
                  Stderr = ""
                  Stdout = c
              } ->
                if c = "" then false else true
                |> Success
            | { ExitCode = exitCode; Stderr = stderr } ->
                if exitCode <> 0 && exitCode <> 1 then
                    raise
                    <| ConversionException
                        {
                            Info = $"Unexpected exit code by spot"
                            DebugInfo = $"Unexpected exit code by spot: %i{exitCode}"
                        }
                else
                    raise
                    <| ConversionException
                        {
                            Info = $"Error by spot"
                            DebugInfo = $"Error by spot: %s{stderr}"
                        }
        with
        | _ when debug -> reraise ()
        | ConversionException err -> Fail(err)
        | e ->
            Fail
                {
                    Info = $"Unexpected error"
                    DebugInfo = $"Unexpected error: %s{e.Message}"
                }
