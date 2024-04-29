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

open System
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
        Info : String // A user-friendly error message that should be displayed to the user
        DebugInfo : String // Additional Information that can be used for debugging 
    }

type AutomataOperationResult<'T> =
    | Success of 'T 
    | Fail of FsOmegaLibError

module AutomataOperationResult = 
    let defaultValue (value: 'T) (result: AutomataOperationResult<'T>) =
        match result with 
        | Success x -> x 
        | Fail _ -> value 

    let defaultWith (defThunk : FsOmegaLibError -> 'T) (result: AutomataOperationResult<'T>) =
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
        | LOW  -> "low"
        | MEDIUM -> "medium"
        | HIGH -> "high"


module private HoaConversion = 

    let private extractAlternatingSkeletonFromHoa (hoaAut : HoaAutomaton) = 
        let header = hoaAut.Header
        let body = hoaAut.Body

        {
            AutomatonSkeleton.States = body.StateMap.Keys |> set
            APs = header.APs;
            Edges = 
                body.StateMap
                |> Map.toSeq
                |> Seq.map (fun (k, (_, e)) -> k, e) 
                |> Map.ofSeq
        }

    let private extractNondeterministicSkeletonFromHoa (hoaAut : HoaAutomaton) = 
        hoaAut
        |> extractAlternatingSkeletonFromHoa
        |> NondeterministicAutomatonSkeleton.tryFromAlternatingAutomatonSkeleton
        |> Option.defaultWith 
            (fun _ -> raise <| ConversionException {Info = $"Could not convert HANOI automaton"; DebugInfo = $"Could not convert HANOI automaton; The HANOI automaton has universal branching"})


    let convertHoaToGNBA (hoaAut : HoaAutomaton) = 
        let header = hoaAut.Header
        let body = hoaAut.Body

        let rec isGNBAAccCondition (cond : AcceptanceCondition) = 
            match cond with 
            | AccAtomFin _ -> false
            | AccAtomInf (PosAcceptanceSet _) -> true
            | AccAtomInf (NegAcceptanceSet _) -> false
            | AccTrue -> true
            | AccFalse -> false
            | AccAnd (l1, l2) -> isGNBAAccCondition l1 && isGNBAAccCondition l2
            | AccOr _ -> false

        let numberOfAccSets, acc =  header.Acceptance

        if isGNBAAccCondition acc |> not then 
            raise <| ConversionException {Info = $"Could not convert HANOI automaton to GNBA"; DebugInfo = $"Could not convert HANOI automaton to GNBA; No valid Acceptance condition for a GNBA: %A{header.Acceptance}"}

        {
            GNBA.Skeleton = 
                extractNondeterministicSkeletonFromHoa hoaAut
            InitialStates = 
                header.Start
                |> List.map (
                    function 
                    | [x] -> x 
                    | _ -> raise <| ConversionException {Info = $"Could not convert HANOI automaton to GNBA"; DebugInfo = $"Could not convert HANOI automaton to GNBA; The HANOI automaton uses conjunctions of initial states"}
                )
                |> set
            AcceptanceSets = 
                body.StateMap
                |> Map.toSeq
                |> Seq.map (fun (k, (a, _)) -> k, a) 
                |> Map.ofSeq
            NumberOfAcceptingSets = numberOfAccSets
        }

    let convertHoaToNBA (hoaAut : HoaAutomaton) = 
        let body = hoaAut.Body

        if hoaAut.Header.Acceptance <> (1, AccAtomInf (PosAcceptanceSet 0)) then 
            raise <| ConversionException {Info = $"Could not convert HANOI automaton to NBA"; DebugInfo = $"Could not convert HANOI automaton to NBA; No valid Acceptance condition for a NBA: %A{hoaAut.Header.Acceptance}"}

        {
            NBA.Skeleton = 
                extractNondeterministicSkeletonFromHoa hoaAut
            InitialStates = 
                hoaAut.Header.Start
                |> List.map (
                    function 
                    | [x] -> x 
                    | _ -> raise <| ConversionException {Info = $"Could not convert HANOI automaton to NBA"; DebugInfo = $"Could not convert HANOI automaton to NBA; The HANOI automaton uses conjunctions of initial states"}
                )
                |> set
            AcceptingStates = 
                body.StateMap
                |> Map.toSeq
                |> Seq.filter 
                    (fun (_, (a, _)) -> 
                        Set.contains 0 a
                    ) 
                |> Seq.map fst
                |> set
        }

    let convertHoaToNSA (hoaAut : HoaAutomaton) = 
        match hoaAut.Header.Acceptance with 
        | 0, AccTrue -> ()
        | _ -> raise <| ConversionException {Info = $"Could not convert HANOI automaton to NSA"; DebugInfo = $"Could not convert HANOI automaton to NSA"}
        
        {
            NSA.Skeleton = extractNondeterministicSkeletonFromHoa hoaAut
            InitialStates = 
                hoaAut.Header.Start
                |> List.map (
                    function 
                    | [x] -> x 
                    | _ -> raise <| ConversionException {Info = $"Could not convert HANOI automaton to NSA"; DebugInfo = $"Could not convert HANOI automaton to NSA; The HANOI automaton uses conjunctions of initial states"}
                )
                |> set
        }
            
    let convertHoaToDPA (hoaAut : HoaAutomaton) = 
        let body = hoaAut.Body

        // Check that the acc condition is a max-even condition
        let rec isParityCondition (_ : AcceptanceCondition) = 
            // TODO, check for parity acceptance
            true

        let _, acc =  hoaAut.Header.Acceptance
        if isParityCondition acc |> not then 
            raise <| ConversionException {Info = $"Could not convert HANOI automaton to DPA"; DebugInfo = $"Could not convert HANOI automaton to DPA; No valid Acceptance condition for a parity automaton: %A{hoaAut.Header.Acceptance}"}

        {
            DPA.Skeleton = 
                extractNondeterministicSkeletonFromHoa hoaAut
            InitialState = 
                match hoaAut.Header.Start with 
                | [[x]] -> x
                | _ -> raise <| ConversionException {Info = $"Could not convert HANOI automaton to DPA"; DebugInfo = $"Could not convert HANOI automaton to DPA; The HOA automaton does not define a unique initial state"}
            Color = 
                body.StateMap
                |> Map.map (fun _ x -> x |> fst |> Set.toList |> List.head)
        }

    let convertHoaToNPA (hoaAut : HoaAutomaton) = 
        let body = hoaAut.Body

        // Check that the acc condition is a max-even condition
        let rec isParityCondition (_ : AcceptanceCondition) = 
            true

        let _, acc =  hoaAut.Header.Acceptance
        if isParityCondition acc |> not then 
            raise <| ConversionException {Info = $"Could not convert HANOI automaton to NPA"; DebugInfo = $"Could not convert HANOI automaton to NPA; No valid Acceptance condition for a parity automaton: %A{hoaAut.Header.Acceptance}"}

        {
            NPA.Skeleton = 
                extractNondeterministicSkeletonFromHoa hoaAut
            InitialStates = 
                hoaAut.Header.Start
                |> List.map (
                    function 
                    | [x] -> x 
                    | _ -> raise <| ConversionException {Info = $"Could not convert HANOI automaton to NPA"; DebugInfo = $"Could not convert HANOI automaton to NPA; The HANOI automaton uses conjunctions of initial states"}
                )
                |> set
            Color = 
                body.StateMap
                |> Map.map (fun _ x -> x |> fst |> Set.toList |> List.head)
        }

    let convertHoaToAPA (hoaAut : HoaAutomaton) = 
        let body = hoaAut.Body

        // Check that the acc condition is a max-even condition
        let rec isParityCondition (_ : AcceptanceCondition) = 
            true

        let _, acc =  hoaAut.Header.Acceptance
        if isParityCondition acc |> not then 
            raise <| ConversionException {Info = $"Could not convert HANOI automaton to APA"; DebugInfo = $"Could not convert HANOI automaton to APA; No valid Acceptance condition for a parity automaton: %A{hoaAut.Header.Acceptance}"}

        {
            APA.Skeleton = extractAlternatingSkeletonFromHoa hoaAut
            InitialStates = 
                hoaAut.Header.Start
                |> List.map set 
                |> set
            Color = 
                body.StateMap
                |> Map.map (fun _ x -> x |> fst |> Set.toList |> List.head)
        }

    let resultToGNBA (res: String) (f : String -> 'L) = 
        match HOA.Parser.parseHoaAutomaton res with 
        | Ok hoa -> 
            convertHoaToGNBA hoa
            |> GNBA.mapAPs f
        | Error err -> raise <| ConversionException {Info = $"Could not parse HANOI automaton"; DebugInfo = $"Could not parse HANOI automaton into GNBA: %s{err}"}
        
    let resultToNBA (res: String) (f : String -> 'L) = 
        match HOA.Parser.parseHoaAutomaton res with 
        | Ok hoa -> 
            convertHoaToNBA hoa
            |> NBA.mapAPs f
        | Error err -> raise <| ConversionException {Info = $"Could not parse HANOI automaton"; DebugInfo = $"Could not parse HANOI automaton into NBA: %s{err}"}

    let resultToDPA (res: String) (f : String -> 'L) = 
        match HOA.Parser.parseHoaAutomaton res with 
        | Ok hoa -> 
            convertHoaToDPA hoa
            |> DPA.mapAPs f
        | Error err -> raise <| ConversionException {Info = $"Could not parse HANOI automaton"; DebugInfo = $"Could not parse HANOI automaton into DPA: %s{err}"}

    let resultToNSA (res: String) (f : String -> 'L) = 
        match HOA.Parser.parseHoaAutomaton res with 
        | Ok hoa -> 
            convertHoaToNSA hoa
            |> NSA.mapAPs f
        | Error err -> raise <| ConversionException {Info = $"Could not parse HANOI automaton"; DebugInfo = $"Could not parse HANOI automaton into NSA: %s{err}"}
    
    let resultToNPA (res: String) (f : String -> 'L) = 
        match HOA.Parser.parseHoaAutomaton res with 
        | Ok hoa -> 
            convertHoaToNPA hoa
            |> NPA.mapAPs f
        | Error err -> raise <| ConversionException {Info = $"Could not parse HANOI automaton"; DebugInfo = $"Could not parse HANOI automaton into NPA: %s{err}"}
    
    let resultToAPA (res: String) (f : String -> 'L) = 
        match HOA.Parser.parseHoaAutomaton res with 
        | Ok hoa -> 
            convertHoaToAPA hoa
            |> APA.mapAPs f
        | Error err -> raise <| ConversionException {Info = $"Could not parse HANOI automaton"; DebugInfo = $"Could not parse HANOI automaton into APA: %s{err}"}
            

module AutomatonConversions = 
    let convertToGNBA (debug : bool) (intermediateFilesPath : String) (autfiltPath : String) (ef : Effort) (aut : AbstractAutomaton<int, 'L>) = 
        try 
            let dict, revDict = 
                aut.Skeleton.APs
                |> List.mapi (fun i x -> 
                    let a = "l" + string i
                    (x, a), (a, x))
                |> List.unzip
                |> fun (x, y) -> Map.ofList x, Map.ofList y

            let s = aut.ToHoaString string (fun x -> dict.[x])

            let path = Path.Combine [|intermediateFilesPath; "aut1.hoa"|]
            let targetPath = Path.Combine [|intermediateFilesPath; "autRes.hoa"|]
        
            File.WriteAllText(path, s)

            let arg = "--small --" + Effort.asString ef + " -S --gba " + path + " -o " + targetPath

            let res = Util.SubprocessUtil.executeSubprocess autfiltPath arg

            match res with 
            | {ExitCode = 0; Stderr = ""} -> 
                let c = File.ReadAllText(targetPath)
                HoaConversion.resultToGNBA c (fun x -> revDict.[x])
                |> Success
            | {ExitCode = exitCode; Stderr = stderr}  -> 
                if exitCode <> 0 then 
                    raise <| ConversionException {Info = $"Unexpected exit code by spot"; DebugInfo = $"Unexpected exit code by spot;  (convert, GNBA); %i{exitCode}"}
                else   
                    raise <| ConversionException {Info = $"Error by spot"; DebugInfo = $"Error by spot; (convert, GNBA); %s{stderr}"}

        with 
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail err
        | e -> 
            Fail {Info = $"Unexpected error"; DebugInfo = $"Unexpected error; (convert, GNBA); %s{e.Message}"}

    let convertToNBA (debug: bool) (intermediateFilesPath : String) (autfiltPath : String) (ef : Effort) (aut : AbstractAutomaton<int, 'L>) = 
        try
            let dict, revDict = 
                aut.Skeleton.APs
                |> List.mapi (fun i x -> 
                    let a = "l" + string i
                    (x, a), (a, x))
                |> List.unzip
                |> fun (x, y) -> Map.ofList x, Map.ofList y

            let s = aut.ToHoaString string (fun x -> dict.[x])

            let path = Path.Combine [|intermediateFilesPath; "aut1.hoa"|]
            let targetPath = Path.Combine [|intermediateFilesPath; "autRes.hoa"|]

            File.WriteAllText(path, s)

            let arg = "--small --" + Effort.asString ef + " -S -B " + path + " -o " + targetPath

            let res = Util.SubprocessUtil.executeSubprocess autfiltPath arg

            match res with 
            | {ExitCode = 0; Stderr = ""} -> 
                let c = File.ReadAllText(targetPath)
                HoaConversion.resultToNBA c (fun x -> revDict.[x])
                |> Success
            | {ExitCode = exitCode; Stderr = stderr}  -> 
                if exitCode <> 0 then 
                    raise <| ConversionException {Info = $"Unexpected exit code by spot"; DebugInfo = $"Unexpected exit code by spot;  (convert, NBA); %i{exitCode}"}
                else   
                    raise <| ConversionException {Info = $"Error by spot"; DebugInfo = $"Error by spot; (convert, NPA); %s{stderr}"}
        with 
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail {Info = $"Unexpected error"; DebugInfo = $"Unexpected error; (convert, NBA); %s{e.Message}"}

    let convertToDPA (debug: bool) (intermediateFilesPath : String) (autfiltPath : String) (ef : Effort) (aut : AbstractAutomaton<int, 'L>) = 
        try 
            let dict, revDict = 
                aut.Skeleton.APs
                |> List.mapi (fun i x -> 
                    let a = "l" + string i
                    (x, a), (a, x))
                |> List.unzip
                |> fun (x, y) -> Map.ofList x, Map.ofList y

            let s = aut.ToHoaString string (fun x -> dict.[x])

            let path = Path.Combine [|intermediateFilesPath; "aut1.hoa"|]
            let targetPath = Path.Combine [|intermediateFilesPath; "autRes.hoa"|]

            File.WriteAllText(path, s)

            let arg = "--small --" + Effort.asString ef + " -D -C -S -p\"max even\" " + path + " -o " + targetPath
            let res = Util.SubprocessUtil.executeSubprocess autfiltPath arg

            match res with 
            | {ExitCode = 0; Stderr = ""} -> 
                let c = File.ReadAllText(targetPath)
                HoaConversion.resultToDPA c (fun x -> revDict.[x])
                |> Success
            | {ExitCode = exitCode; Stderr = stderr}  -> 
                if exitCode <> 0 then 
                    raise <| ConversionException {Info = $"Unexpected exit code by spot"; DebugInfo = $"Unexpected exit code by spot;  (convert, DPA); %i{exitCode}"}
                else   
                    raise <| ConversionException {Info = $"Error by spot"; DebugInfo = $"Error by spot; (convert, DPA); %s{stderr}"}
        with
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail {Info = $"Unexpected error"; DebugInfo = $"Unexpected error; (convert, DPA); %s{e.Message}"}

    let convertToNPA (debug: bool) (intermediateFilesPath : String) (autfiltPath : String) (ef : Effort) (aut : AbstractAutomaton<int, 'L>) = 
        try 
            let dict, revDict = 
                aut.Skeleton.APs
                |> List.mapi (fun i x -> 
                    let a = "l" + string i
                    (x, a), (a, x))
                |> List.unzip
                |> fun (x, y) -> Map.ofList x, Map.ofList y

            let s = aut.ToHoaString string (fun x -> dict.[x])

            let path = Path.Combine [|intermediateFilesPath; "aut1.hoa"|]
            let targetPath = Path.Combine [|intermediateFilesPath; "autRes.hoa"|]

            File.WriteAllText(path, s)

            let arg = "--small --" + Effort.asString ef + " -S -p\"max even\" " + path + " -o " + targetPath
            let res = Util.SubprocessUtil.executeSubprocess autfiltPath arg

            match res with 
            | {ExitCode = 0; Stderr = ""} -> 
                let c = File.ReadAllText(targetPath)
                HoaConversion.resultToNPA c (fun x -> revDict.[x])
                |> Success
            | {ExitCode = exitCode; Stderr = stderr}  -> 
                if exitCode <> 0 then 
                    raise <| ConversionException {Info = $"Unexpected exit code by spot"; DebugInfo = $"Unexpected exit code by spot;  (convert, NPA); %i{exitCode}"}
                else   
                    raise <| ConversionException {Info = $"Error by spot"; DebugInfo = $"Error by spot; (convert, NPA); %s{stderr}"}
        with
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail {Info = $"Unexpected error"; DebugInfo = $"Unexpected error; (convert, NPA); %s{e.Message}"}

    let convertToNSA (debug: bool) (intermediateFilesPath : String) (autfiltPath : String) (ef : Effort) (aut : AbstractAutomaton<int, 'L>) = 
        try
            let dict, revDict = 
                aut.Skeleton.APs
                |> List.mapi (fun i x -> 
                    let a = "l" + string i
                    (x, a), (a, x))
                |> List.unzip
                |> fun (x, y) -> Map.ofList x, Map.ofList y

            let s = aut.ToHoaString string (fun x -> dict.[x])

            let path = Path.Combine [|intermediateFilesPath; "aut1.hoa"|]
            let targetPath = Path.Combine [|intermediateFilesPath; "autRes.hoa"|]

            File.WriteAllText(path, s)

            let arg = "--small --" + Effort.asString ef + " -M " + path + " -o " + targetPath

            let res = Util.SubprocessUtil.executeSubprocess autfiltPath arg

            match res with 
            | {ExitCode = 0; Stderr = ""} -> 
                let c = File.ReadAllText(targetPath)
                HoaConversion.resultToNSA c (fun x -> revDict.[x])
                |> Success
            | {ExitCode = exitCode; Stderr = stderr}  -> 
                if exitCode <> 0 then 
                    raise <| ConversionException {Info = $"Unexpected exit code by spot"; DebugInfo = $"Unexpected exit code by spot;  (convert, NSA); %i{exitCode}"}
                else   
                    raise <| ConversionException {Info = $"Error by spot"; DebugInfo = $"Error by spot; (convert, NSA); %s{stderr}"}
        with 
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail {Info = $"Unexpected error"; DebugInfo = $"Unexpected error; (convert, NSA); %s{e.Message}"}


module AutomatonFromString = 
    let convertHoaStringToGNBA (debug : bool) (intermediateFilesPath : String) (autfiltPath : String) (ef : Effort) (autString : String) = 
        try 
            let path = Path.Combine [|intermediateFilesPath; "aut1.hoa"|]
            let targetPath = Path.Combine [|intermediateFilesPath; "autRes.hoa"|]
        
            File.WriteAllText(path, autString)

            let arg = "--small --" + Effort.asString ef + " -S --gba " + path + " -o " + targetPath

            let res = Util.SubprocessUtil.executeSubprocess autfiltPath arg

            match res with 
            | {ExitCode = 0; Stderr = ""} -> 
                let c = File.ReadAllText(targetPath)
                HoaConversion.resultToGNBA c id
                |> Success
            | {ExitCode = exitCode; Stderr = stderr}  -> 
                if exitCode <> 0 then 
                    raise <| ConversionException {Info = $"Unexpected exit code by spot"; DebugInfo = $"Unexpected exit code by spot;  (convert, GNBA, string); %i{exitCode}"}
                else   
                    raise <| ConversionException {Info = $"Error by spot"; DebugInfo = $"Error by spot; (convert, GNBA, string); %s{stderr}"}

        with 
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail {Info = $"Unexpected error"; DebugInfo = $"Unexpected error; (convert, GNBA, string); %s{e.Message}"}

    let convertHoaStringToNBA (debug: bool) (intermediateFilesPath : String) (autfiltPath : String) (ef : Effort) (autString : String) = 
        try
            let path = Path.Combine [|intermediateFilesPath; "aut1.hoa"|]
            let targetPath = Path.Combine [|intermediateFilesPath; "autRes.hoa"|]

            File.WriteAllText(path, autString)

            let arg = "--small --" + Effort.asString ef + " -S -B " + path + " -o " + targetPath

            let res = Util.SubprocessUtil.executeSubprocess autfiltPath arg

            match res with 
            | {ExitCode = 0; Stderr = ""} -> 
                let c = File.ReadAllText(targetPath)
                HoaConversion.resultToNBA c id
                |> Success
            | {ExitCode = exitCode; Stderr = stderr}  -> 
                if exitCode <> 0 then 
                    raise <| ConversionException {Info = $"Unexpected exit code by spot"; DebugInfo = $"Unexpected exit code by spot;  (convert, NBA, string); %i{exitCode}"}
                else   
                    raise <| ConversionException {Info = $"Error by spot"; DebugInfo = $"Error by spot; (convert, NBA, string); %s{stderr}"}
        with 
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail {Info = $"Unexpected error"; DebugInfo = $"Unexpected error; (convert, NBA, string); %s{e.Message}"}

    let convertHoaStringToDPA (debug: bool) (intermediateFilesPath : String) (autfiltPath : String) (ef : Effort) (autString : String) = 
        try 
            let path = Path.Combine [|intermediateFilesPath; "aut1.hoa"|]
            let targetPath = Path.Combine [|intermediateFilesPath; "autRes.hoa"|]

            File.WriteAllText(path, autString)

            let arg = "--small --" + Effort.asString ef + " -D -C -S -p\"max even\" " + path + " -o " + targetPath
            let res = Util.SubprocessUtil.executeSubprocess autfiltPath arg

            match res with 
            | {ExitCode = 0; Stderr = ""} -> 
                let c = File.ReadAllText(targetPath)
                HoaConversion.resultToDPA c id
                |> Success
            | {ExitCode = exitCode; Stderr = stderr}  -> 
                if exitCode <> 0 then 
                    raise <| ConversionException {Info = $"Unexpected exit code by spot"; DebugInfo = $"Unexpected exit code by spot;  (convert, DPA, string); %i{exitCode}"}
                else   
                    raise <| ConversionException {Info = $"Error by spot"; DebugInfo = $"Error by spot; (convert, DPA, string); %s{stderr}"}
        with
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail {Info = $"Unexpected error"; DebugInfo = $"Unexpected error; (convert, DPA, string); %s{e.Message}"}

   
module AutomataOperations = 
    let complementToGNBA debug (intermediateFilesPath : String) (autfiltPath : String) (ef : Effort) (aut : AbstractAutomaton<int, 'L>) = 
        try
            let dict, revDict = 
                aut.Skeleton.APs
                |> List.mapi (fun i x -> 
                    let a = "l" + string i
                    (x, a), (a, x))
                |> List.unzip
                |> fun (x, y) -> Map.ofList x, Map.ofList y

            let s = aut.ToHoaString string (fun x -> dict.[x])

            let path = Path.Combine [|intermediateFilesPath; "aut1.hoa"|]
            let targetPath = Path.Combine [|intermediateFilesPath; "autRes.hoa"|]

            File.WriteAllText(path, s)

            let arg = "--small --" + Effort.asString ef + " -S --gba --complement " + path + " -o " + targetPath

            let res = Util.SubprocessUtil.executeSubprocess autfiltPath arg
            
            match res with 
            | {ExitCode = 0; Stderr = ""} -> 
                let c = File.ReadAllText(targetPath)
                HoaConversion.resultToGNBA c (fun x -> revDict.[x])
                |> Success
            | {ExitCode = exitCode; Stderr = stderr}  -> 
                if exitCode <> 0 then 
                    raise <| ConversionException {Info = $"Unexpected exit code by spot"; DebugInfo = $"Unexpected exit code by spot;  (complement, GNBA); %i{exitCode}"}
                else   
                    raise <| ConversionException {Info = $"Error by spot"; DebugInfo = $"Error by spot; (complement, GNBA); %s{stderr}"}
        with
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail {Info = $"Unexpected error"; DebugInfo = $"Unexpected error; (complement, GNBA); %s{e.Message}"}

    let complementToNBA debug (intermediateFilesPath : String) (autfiltPath : String) (ef : Effort) (aut : AbstractAutomaton<int, 'L>) = 
        try 
            let dict, revDict = 
                aut.Skeleton.APs
                |> List.mapi (fun i x -> 
                    let a = "l" + string i
                    (x, a), (a, x))
                |> List.unzip
                |> fun (x, y) -> Map.ofList x, Map.ofList y

            let s = aut.ToHoaString string (fun x -> dict.[x])

            let path = Path.Combine [|intermediateFilesPath; "aut1.hoa"|]
            let targetPath = Path.Combine [|intermediateFilesPath; "autRes.hoa"|]

            File.WriteAllText(path, s)

            let arg = "--small --" + Effort.asString ef + " -S -B --complement " + path + " -o " + targetPath

            let res = Util.SubprocessUtil.executeSubprocess autfiltPath arg
            
            match res with 
            | {ExitCode = 0; Stderr = ""} -> 
                let c = File.ReadAllText(targetPath)
                HoaConversion.resultToNBA c (fun x -> revDict.[x])
                |> Success
            | {ExitCode = exitCode; Stderr = stderr}  -> 
                if exitCode <> 0 then 
                    raise <| ConversionException {Info = $"Unexpected exit code by spot"; DebugInfo = $"Unexpected exit code by spot;  (complement, NBA); %i{exitCode}"}
                else   
                    raise <| ConversionException {Info = $"Error by spot"; DebugInfo = $"Error by spot; (complement, NBA); %s{stderr}"}

        with
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail {Info = $"Unexpected error"; DebugInfo = $"Unexpected error; (complement, NBA); %s{e.Message}"}

    let unionToGNBA debug (intermediateFilesPath : String) (autfiltPath : String) (ef : Effort) (aut1 : AbstractAutomaton<int, 'L>) (aut2 : AbstractAutomaton<int, 'L>) = 
        try
            let dict, revDict = 
                aut1.Skeleton.APs @ aut2.Skeleton.APs
                |> List.distinct
                |> List.mapi (fun i x -> 
                    let a = "l" + string i
                    (x, a), (a, x))
                |> List.unzip
                |> fun (x, y) -> Map.ofList x, Map.ofList y

            let s1 = aut1.ToHoaString string (fun x -> dict.[x])
            let s2 = aut2.ToHoaString string (fun x -> dict.[x])

            let path1 = Path.Combine [|intermediateFilesPath; "aut1.hoa"|]
            let path2 = Path.Combine [|intermediateFilesPath; "aut2.hoa"|]
            let targetPath = Path.Combine [|intermediateFilesPath; "autRes.hoa"|]

            File.WriteAllText(path1, s1)
            File.WriteAllText(path2, s2)

            let arg = "--small --" + Effort.asString ef + " --product-or=" + path2 + " -S --gba " + path1 + " -o " + targetPath

            let res = Util.SubprocessUtil.executeSubprocess autfiltPath arg

            match res with 
            | {ExitCode = 0; Stderr = ""} -> 
                let c = File.ReadAllText(targetPath)
                HoaConversion.resultToGNBA c (fun x -> revDict.[x])
                |> Success
            | {ExitCode = exitCode; Stderr = stderr}  -> 
                if exitCode <> 0 then 
                    raise <| ConversionException {Info = $"Unexpected exit code by spot"; DebugInfo = $"Unexpected exit code by spot;  (union, GNBA); %i{exitCode}"}
                else   
                    raise <| ConversionException {Info = $"Error by spot"; DebugInfo = $"Error by spot; (union, GNBA); %s{stderr}"}
        with
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail {Info = $"Unexpected error"; DebugInfo = $"Unexpected error; (union, GNBA); %s{e.Message}"}

    let intersectToGNBA debug (intermediateFilesPath : String) (autfiltPath : String) (ef : Effort) (aut1 : AbstractAutomaton<int, 'L>) (aut2 : AbstractAutomaton<int, 'L>) = 
        try 
            let dict, revDict = 
                aut1.Skeleton.APs @ aut2.Skeleton.APs
                |> List.distinct
                |> List.mapi (fun i x -> 
                    let a = "l" + string i
                    (x, a), (a, x))
                |> List.unzip
                |> fun (x, y) -> Map.ofList x, Map.ofList y

            let s1 = aut1.ToHoaString string (fun x -> dict.[x])
            let s2 = aut2.ToHoaString string (fun x -> dict.[x])

            let path1 = Path.Combine [|intermediateFilesPath; "aut1.hoa"|]
            let path2 = Path.Combine [|intermediateFilesPath; "aut2.hoa"|]
            let targetPath = Path.Combine [|intermediateFilesPath; "autRes.hoa"|]

            File.WriteAllText(path1, s1)
            File.WriteAllText(path2, s2)

            let arg = "--small --" + Effort.asString ef + " --product=" + path2 + " -S --gba " + path1 + " -o " + targetPath

            let res = Util.SubprocessUtil.executeSubprocess autfiltPath arg

            match res with 
            | {ExitCode = 0; Stderr = ""} -> 
                let c = File.ReadAllText(targetPath)
                HoaConversion.resultToGNBA c (fun x -> revDict.[x])
                |> Success
            | {ExitCode = exitCode; Stderr = stderr}  -> 
                if exitCode <> 0 then 
                    raise <| ConversionException {Info = $"Unexpected exit code by spot"; DebugInfo = $"Unexpected exit code by spot;  (intersect, GNBA); %i{exitCode}"}
                else   
                    raise <| ConversionException {Info = $"Error by spot"; DebugInfo = $"Error by spot; (intersect, GNBA); %s{stderr}"}
        with
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail {Info = $"Unexpected error"; DebugInfo = $"Unexpected error; (intersect, GNBA); %s{e.Message}"}

module LTLConversion = 

    let convertLTLtoGNBA debug (intermediateFilesPath : String) (ltl2tgbaPath : String) (ltl : LTL<'L>)  = 
        try 
            let dict, revDict = 
                ltl 
                |> LTL.allAtoms
                |> Set.toList
                |> List.mapi (fun i x -> 
                    let a = "l" + string i
                    (x, a), (a, x))
                |> List.unzip
                |> fun (x, y) -> Map.ofList x, Map.ofList y
            
            let ltlAsString = 
                ltl
                |> LTL.printInSpotFormat (fun x -> "\"" + dict.[x] + "\"")

            let targetPath = Path.Combine [|intermediateFilesPath; "autRes.hoa"|]

            let args = "-S --gba \"" + ltlAsString + "\"" + " -o " + targetPath

            let res = Util.SubprocessUtil.executeSubprocess ltl2tgbaPath args

            match res with 
            | {ExitCode = 0; Stderr = ""} -> 
                let c = File.ReadAllText(targetPath)
                HoaConversion.resultToGNBA c (fun x -> revDict.[x])
                |> Success
            | {ExitCode = exitCode; Stderr = stderr}  -> 
                if exitCode <> 0 then 
                    raise <| ConversionException {Info = $"Unexpected exit code by spot"; DebugInfo = $"Unexpected exit code by spot;  (LTL, GNBA); %i{exitCode}"}
                else   
                    raise <| ConversionException {Info = $"Error by spot"; DebugInfo = $"Error by spot; (LTL, GNBA); %s{stderr}"}
        with
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail {Info = $"Unexpected error"; DebugInfo = $"Unexpected error; (LTL, GNBA); %s{e.Message}"}

    let convertLTLtoNBA debug (intermediateFilesPath : String) (ltl2tgbaPath : String) (ltl : LTL<'L>)  = 
        try 
            let dict, revDict = 
                ltl 
                |> LTL.allAtoms
                |> Set.toList
                |> List.mapi (fun i x -> 
                    let a = "l" + string i
                    (x, a), (a, x))
                |> List.unzip
                |> fun (x, y) -> Map.ofList x, Map.ofList y
            
            let ltlAsString = 
                ltl
                |> LTL.printInSpotFormat (fun x -> "\"" + dict.[x] + "\"")

            let targetPath = Path.Combine [|intermediateFilesPath; "autRes.hoa"|]

            let args = "-S -B \"" + ltlAsString + "\"" + " -o " + targetPath

            let res = Util.SubprocessUtil.executeSubprocess ltl2tgbaPath args

            match res with 
            | {ExitCode = 0; Stderr = ""} -> 
                let c = File.ReadAllText(targetPath)
                HoaConversion.resultToNBA c (fun x -> revDict.[x])
                |> Success
            | {ExitCode = exitCode; Stderr = stderr}  -> 
                if exitCode <> 0 then 
                    raise <| ConversionException {Info = $"Unexpected exit code by spot"; DebugInfo = $"Unexpected exit code by spot;  (LTL, NBA); %i{exitCode}"}
                else   
                    raise <| ConversionException {Info = $"Error by spot"; DebugInfo = $"Error by spot; (ltl, NBA); %s{stderr}"}
        with
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail {Info = $"Unexpected error"; DebugInfo = $"Unexpected error; (LTL, NBA); %s{e.Message}"}

    let convertLTLtoDPA debug (intermediateFilesPath : String) (ltl2tgbaPath : String) (ltl : LTL<'L>)  = 
        try 
            let dict, revDict = 
                ltl 
                |> LTL.allAtoms
                |> Set.toList
                |> List.mapi (fun i x -> 
                    let a = "l" + string i
                    (x, a), (a, x))
                |> List.unzip
                |> fun (x, y) -> Map.ofList x, Map.ofList y
            
            let ltlAsString = 
                ltl
                |> LTL.printInSpotFormat (fun x -> "\"" + dict.[x] + "\"")

            let targetPath = Path.Combine [|intermediateFilesPath; "autRes.hoa"|]

            let args = "-S -C -D -p\"max even\" \"" + ltlAsString + "\"" + " -o " + targetPath

            let res = Util.SubprocessUtil.executeSubprocess ltl2tgbaPath args

            match res with 
            | {ExitCode = 0; Stderr = ""} -> 
                let c = File.ReadAllText(targetPath)
                HoaConversion.resultToDPA c (fun x -> revDict.[x])
                |> Success
            | {ExitCode = exitCode; Stderr = stderr}  -> 
                if exitCode <> 0 then 
                    raise <| ConversionException {Info = $"Unexpected exit code by spot"; DebugInfo = $"Unexpected exit code by spot;  (LTL, DPA); %i{exitCode}"}
                else   
                    raise <| ConversionException {Info = $"Error by spot"; DebugInfo = $"Error by spot; (ltl, DPA); %s{stderr}"}
        with
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail {Info = $"Unexpected error"; DebugInfo = $"Unexpected error; (LTL, DPA); %s{e.Message}"}

    let convertLTLtoNSA debug (intermediateFilesPath : String) (ltl2tgbaPath : String) (ltl : LTL<'L>)  = 
        try 
            let dict, revDict = 
                ltl 
                |> LTL.allAtoms
                |> Set.toList
                |> List.mapi (fun i x -> 
                    let a = "l" + string i
                    (x, a), (a, x))
                |> List.unzip
                |> fun (x, y) -> Map.ofList x, Map.ofList y
            
            let ltlAsString = 
                ltl
                |> LTL.printInSpotFormat (fun x -> "\"" + dict.[x] + "\"")

            let targetPath = Path.Combine [|intermediateFilesPath; "autRes.hoa"|]

            let args = "-M \"" + ltlAsString + "\"" + " -o " + targetPath

            let res = Util.SubprocessUtil.executeSubprocess ltl2tgbaPath args

            match res with 
            | {ExitCode = 0; Stderr = ""} -> 
                let c = File.ReadAllText(targetPath)
                HoaConversion.resultToNSA c (fun x -> revDict.[x])
                |> Success
            | {ExitCode = exitCode; Stderr = stderr}  -> 
                if exitCode <> 0 then 
                    raise <| ConversionException {Info = $"Unexpected exit code by spot"; DebugInfo = $"Unexpected exit code by spot;  (LTL, NSA); %i{exitCode}"}
                else   
                    raise <| ConversionException {Info = $"Error by spot"; DebugInfo = $"Error by spot; (ltl, NSA); %s{stderr}"}
        with
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail {Info = $"Unexpected error"; DebugInfo = $"Unexpected error; (LTL, NSA); %s{e.Message}"}


module AutomataChecks = 
    let isEmpty debug (intermediateFilesPath : String) (autfiltPath : String) (aut : AbstractAutomaton<int, 'L>) = 
        try
            let dict = 
                aut.Skeleton.APs
                |> List.mapi (fun i x -> 
                    let a = "l" + string i
                    (x, a))
                |> Map.ofList

            let s = aut.ToHoaString string (fun x -> dict.[x])
            
            let path = Path.Combine [|intermediateFilesPath; "aut1.hoa"|]
            File.WriteAllText(path, s)

            let args = "--is-empty " + path

            let res = Util.SubprocessUtil.executeSubprocess autfiltPath args

            match res with 
            | {ExitCode = 0; Stderr = ""; Stdout = c} | {ExitCode = 1; Stderr = ""; Stdout = c} -> 
                if c = "" then false else true
                |> Success
            | {ExitCode = exitCode; Stderr = stderr}  -> 
                if exitCode <> 0 && exitCode <> 1 then 
                    raise <| ConversionException {Info = $"Unexpected exit code by spot"; DebugInfo = $"Unexpected exit code by spot;  (emptiness); %i{exitCode}"}
                else   
                    raise <| ConversionException {Info = $"Error by spot"; DebugInfo = $"Error by spot; (emptiness); %s{stderr}"}
        with
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail {Info = $"Unexpected error"; DebugInfo = $"Unexpected error; (emptiness); %s{e.Message}"}

    let isContained debug (intermediateFilesPath : String) (autfiltPath : String) (aut1 : AbstractAutomaton<int, 'L>) (aut2 : AbstractAutomaton<int, 'L>)  = 
        try 
            let dict = 
                aut1.Skeleton.APs @ aut2.Skeleton.APs
                |> List.distinct
                |> List.mapi (fun i x -> 
                    let a = "l" + string i
                    (x, a))
                |> Map.ofList

            let s1 = aut1.ToHoaString string (fun x -> dict.[x])
            let s2 = aut2.ToHoaString string (fun x -> dict.[x])
            
            let path1 = Path.Combine [|intermediateFilesPath; "aut1.hoa"|]
            let path2 = Path.Combine [|intermediateFilesPath; "aut2.hoa"|]

            File.WriteAllText(path1, s1)
            File.WriteAllText(path2, s2)

            let arg = "--included-in=" + path2 + " " + path1
            let res = Util.SubprocessUtil.executeSubprocess autfiltPath arg

            match res with 
            | {ExitCode = 0; Stderr = ""; Stdout = c} | {ExitCode = 1; Stderr = ""; Stdout = c} -> 
                if c = "" then false else true
                |> Success
            | {ExitCode = exitCode; Stderr = stderr}  -> 
                if exitCode <> 0 && exitCode <> 1 then 
                    raise <| ConversionException {Info = $"Unexpected exit code by spot"; DebugInfo = $"Unexpected exit code by spot;  (containment); %i{exitCode}"}
                else   
                    raise <| ConversionException {Info = $"Error by spot"; DebugInfo = $"Error by spot; (containment); %s{stderr}"}
        with
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail {Info = $"Unexpected error"; DebugInfo = $"Unexpected error; (containment); %s{e.Message}"}

    let isEquivalent debug (intermediateFilesPath : String) (autfiltPath : String) (aut1 : AbstractAutomaton<int, 'L>) (aut2 : AbstractAutomaton<int, 'L>) = 
        try
            let dict =
                aut1.Skeleton.APs @ aut2.Skeleton.APs
                |> List.distinct
                |> List.mapi (fun i x -> 
                    let a = "l" + string i
                    (x, a))
                |> Map.ofList

            let s1 = aut1.ToHoaString string (fun x -> dict.[x])
            let s2 = aut2.ToHoaString string (fun x -> dict.[x])

            let path1 = Path.Combine [|intermediateFilesPath; "aut1.hoa"|]
            let path2 = Path.Combine [|intermediateFilesPath; "aut2.hoa"|]

            File.WriteAllText(path1, s1)
            File.WriteAllText(path2, s2)

            let arg = "--equivalent-to=" + path2 + " " + path1
            let res = Util.SubprocessUtil.executeSubprocess autfiltPath arg

            match res with 
            | {ExitCode = 0; Stderr = ""; Stdout = c} | {ExitCode = 1; Stderr = ""; Stdout = c} -> 
                if c = "" then false else true
                |> Success
            | {ExitCode = exitCode; Stderr = stderr}  -> 
                if exitCode <> 0 && exitCode <> 1 then 
                    raise <| ConversionException {Info = $"Unexpected exit code by spot"; DebugInfo = $"Unexpected exit code by spot;  (equivalence); %i{exitCode}"}
                else   
                    raise <| ConversionException {Info = $"Error by spot"; DebugInfo = $"Error by spot; (equivalence); %s{stderr}"}
        with
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail {Info = $"Unexpected error"; DebugInfo = $"Unexpected error; (equivalence); %s{e.Message}"}
