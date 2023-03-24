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

module FsOmegaLib.Conversion

open System
open System.IO

open Util.SystemCallUtil
open HOA
open AbstractAutomaton
open GNBA
open NBA
open DPA
open LTL

type AutomataConversionResult<'T> =
    | Success of 'T 
    | Timeout 
    | Fail of String

exception internal ConversionException of String

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

        let numberOfAccSets =  
            match header.Acceptance with 
            | Some (numberOfAccSets: int, acc) when isGNBAAccCondition acc -> numberOfAccSets
            | _ -> raise <| ConversionException $"No valid Acceptance condition for a GNBA: %A{header.Acceptance}"

        {
            GNBA.Skeleton = 
                {
                    States = set([0..header.States.Value - 1]);
                    APs = header.APs.Value;
                    Edges = 
                        body.StateMap
                        |> Map.toSeq
                        |> Seq.map 
                            (fun (k, (_, e)) -> 
                                k, e
                            ) 
                        |> Map.ofSeq
                }
            InitialStates = header.Start |> set
            AcceptanceSets = 
                body.StateMap
                |> Map.toSeq
                |> Seq.map 
                    (fun (k, (a, _)) -> 
                        k, a
                    ) 
                |> Map.ofSeq
            NumberOfAcceptingSets = numberOfAccSets
        }

    let convertHoaToNBA (hoaAut : HoaAutomaton) = 
        let body = hoaAut.Body

        match hoaAut.Header.Acceptance with 
        | Some (1, AccAtomInf (PosAcceptanceSet 0)) -> ()
        | _ -> raise <| ConversionException $"No valid NBA-Acceptance condition: %A{hoaAut.Header.Acceptance}" 
        
        {
            NBA.Skeleton = 
                {
                    States = set([0..hoaAut.Header.States.Value - 1]);
                    APs = hoaAut.Header.APs.Value;
                    Edges = 
                        body.StateMap
                        |> Map.toSeq
                        |> Seq.map 
                            (fun (k, (_, e)) -> 
                                k, e
                            ) 
                        |> Map.ofSeq
                }
            InitialStates = hoaAut.Header.Start |> set
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
            
    let convertHoaToDPA (hoaAut : HoaAutomaton) = 
        let body = hoaAut.Body

        let rec isParityCondition (_ : AcceptanceCondition) = 
            // TODO
            true

        match hoaAut.Header.Acceptance with 
        | Some (_, acc) when isParityCondition acc -> ()
        | _ -> raise <| ConversionException $"No valid DPA-Acceptance condition: %A{hoaAut.Header.Acceptance}" 
        
        {
            DPA.Skeleton = 
                {
                    States = set([0..hoaAut.Header.States.Value - 1]);
                    APs = hoaAut.Header.APs.Value;
                    Edges = 
                        body.StateMap
                        |> Map.toSeq
                        |> Seq.map 
                            (fun (k, (_, e)) -> 
                                k, e
                            ) 
                        |> Map.ofSeq
                }
            InitialState = hoaAut.Header.Start |> List.head
            Color = 
                body.StateMap
                |> Map.map (fun _ x -> x |> fst |> Set.toList |> List.head)
        }

    let resultToGNBA (res: String) (f : String -> 'L) = 
        match HOA.Parser.parseHoaAutomaton res with 
        | Ok hoa -> 
            convertHoaToGNBA hoa
            |> GNBA.mapAPs f
        | Error err -> raise <| ConversionException err
        
    let resultToNBA (res: String) (f : String -> 'L) = 
        match HOA.Parser.parseHoaAutomaton res with 
        | Ok hoa -> 
            convertHoaToNBA hoa
            |> NBA.mapAPs f
        | Error err -> raise <| ConversionException err

    let resultToDPA (res: String) (f : String -> 'L) = 
        match HOA.Parser.parseHoaAutomaton res with 
        | Ok hoa -> 
            convertHoaToDPA hoa
            |> DPA.mapAPs f
        | Error err -> raise <| ConversionException err
            

module AutomatonConversions = 
    let convertToGNBA (debug : bool) (intermediateFilesPath : String) (autfiltPath : String) (ef : Effort) timeout (aut : AbstractAutomaton<int, 'L>) = 
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

            let res = Util.SystemCallUtil.systemCall autfiltPath arg timeout

            match res with 
            | SystemCallSuccess _ -> 
                let c = File.ReadAllText(targetPath)
                HoaConversion.resultToGNBA c (fun x -> revDict.[x]) 
                |> Success
            | SystemCallTimeout -> 
                Timeout
            | SystemCallError err -> 
                Fail err
        with 
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail ($"%s{e.Message}")

    let convertToNBA (debug: bool) (intermediateFilesPath : String) (autfiltPath : String) (ef : Effort) timeout (aut : AbstractAutomaton<int, 'L>) = 
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

            let res = Util.SystemCallUtil.systemCall autfiltPath arg timeout

            match res with 
            | SystemCallSuccess _ -> 
                let c = File.ReadAllText(targetPath)
                HoaConversion.resultToNBA c (fun x -> revDict.[x]) 
                |> Success
            | SystemCallTimeout -> 
                Timeout
            | SystemCallError err -> 
                Fail (err)
        with 
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail ($"%s{e.Message}")

    let convertToDPA (debug: bool) (intermediateFilesPath : String) (autfiltPath : String) (ef : Effort) timeout (aut : AbstractAutomaton<int, 'L>) = 
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
            let res = Util.SystemCallUtil.systemCall autfiltPath arg timeout

            match res with 
            | SystemCallSuccess _ -> 
                let c = File.ReadAllText(targetPath)
                HoaConversion.resultToDPA c (fun x -> revDict.[x]) 
                |> Success
            | SystemCallTimeout -> 
                Timeout
            | SystemCallError err -> 
                Fail (err)
        with
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail ($"%s{e.Message}")

module AutomatonFromString = 
    let convertHoaStringToGNBA (debug : bool) (intermediateFilesPath : String) (autfiltPath : String) (ef : Effort) timeout (autString : String) = 
        try 
            let path = Path.Combine [|intermediateFilesPath; "aut1.hoa"|]
            let targetPath = Path.Combine [|intermediateFilesPath; "autRes.hoa"|]
        
            File.WriteAllText(path, autString)

            let arg = "--small --" + Effort.asString ef + " -S --gba " + path + " -o " + targetPath

            let res = Util.SystemCallUtil.systemCall autfiltPath arg timeout

            match res with 
            | SystemCallSuccess _ -> 
                let c = File.ReadAllText(targetPath)
                HoaConversion.resultToGNBA c id
                |> Success
            | SystemCallTimeout -> 
                Timeout
            | SystemCallError err -> 
                Fail err
        with 
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail ($"%s{e.Message}")

    let convertHoaStringToNBA (debug: bool) (intermediateFilesPath : String) (autfiltPath : String) (ef : Effort) timeout (autString : String) = 
        try
            let path = Path.Combine [|intermediateFilesPath; "aut1.hoa"|]
            let targetPath = Path.Combine [|intermediateFilesPath; "autRes.hoa"|]

            File.WriteAllText(path, autString)

            let arg = "--small --" + Effort.asString ef + " -S -B " + path + " -o " + targetPath

            let res = Util.SystemCallUtil.systemCall autfiltPath arg timeout

            match res with 
            | SystemCallSuccess _ -> 
                let c = File.ReadAllText(targetPath)
                HoaConversion.resultToNBA c id
                |> Success
            | SystemCallTimeout -> 
                Timeout
            | SystemCallError err -> 
                Fail (err)
        with 
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail ($"%s{e.Message}")

    let convertHoaStringToDPA (debug: bool) (intermediateFilesPath : String) (autfiltPath : String) (ef : Effort) timeout (autString : String) = 
        try 
            let path = Path.Combine [|intermediateFilesPath; "aut1.hoa"|]
            let targetPath = Path.Combine [|intermediateFilesPath; "autRes.hoa"|]

            File.WriteAllText(path, autString)

            let arg = "--small --" + Effort.asString ef + " -D -C -S -p\"max even\" " + path + " -o " + targetPath
            let res = Util.SystemCallUtil.systemCall autfiltPath arg timeout

            match res with 
            | SystemCallSuccess _ -> 
                let c = File.ReadAllText(targetPath)
                HoaConversion.resultToDPA c id
                |> Success
            | SystemCallTimeout -> 
                Timeout
            | SystemCallError err -> 
                Fail (err)
        with
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail ($"%s{e.Message}")

   
module AutomataOperations = 
    let complementToGNBA debug (intermediateFilesPath : String) (autfiltPath : String) (ef : Effort) timeout (aut : AbstractAutomaton<int, 'L>) = 
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

            let res = Util.SystemCallUtil.systemCall autfiltPath arg timeout
            
            match res with 
            | SystemCallSuccess _ -> 
                let c = File.ReadAllText(targetPath)
                HoaConversion.resultToGNBA c (fun x -> revDict.[x]) 
                |> Success
            | SystemCallTimeout -> 
                Timeout
            | SystemCallError err -> 
                Fail err
        with
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail ($"%s{e.Message}")

    let complementToNBA debug (intermediateFilesPath : String) (autfiltPath : String) (ef : Effort) timeout (aut : AbstractAutomaton<int, 'L>) = 
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

            let res = Util.SystemCallUtil.systemCall autfiltPath arg timeout
            
            match res with 
            | SystemCallSuccess _ -> 
                let c = File.ReadAllText(targetPath)
                HoaConversion.resultToNBA c (fun x -> revDict.[x]) 
                |> Success
            | SystemCallTimeout -> 
                Timeout
            | SystemCallError err -> 
                Fail err

        with
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail ($"%s{e.Message}")

    let unionToGNBA debug (intermediateFilesPath : String) (autfiltPath : String) (ef : Effort) timeout (aut1 : AbstractAutomaton<int, 'L>) (aut2 : AbstractAutomaton<int, 'L>) = 
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

            let res = Util.SystemCallUtil.systemCall autfiltPath arg timeout

            match res with 
            | SystemCallSuccess _ -> 
                let c = File.ReadAllText(targetPath)
                HoaConversion.resultToGNBA c (fun x -> revDict.[x]) 
                |> Success  
            | SystemCallTimeout -> 
                Timeout
            | SystemCallError err -> 
                Fail err
        with
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail ($"%s{e.Message}")

    let intersectToGNBA debug (intermediateFilesPath : String) (autfiltPath : String) (ef : Effort) timeout (aut1 : AbstractAutomaton<int, 'L>) (aut2 : AbstractAutomaton<int, 'L>) = 
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

            let res = Util.SystemCallUtil.systemCall autfiltPath arg timeout

            match res with 
            | SystemCallSuccess _ -> 
                let c = File.ReadAllText(targetPath)
                HoaConversion.resultToGNBA c (fun x -> revDict.[x]) 
                |> Success 
            | SystemCallTimeout -> 
                Timeout
            | SystemCallError err -> 
                Fail err
        with
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail ($"%s{e.Message}")

module LTLConversion = 

    let convertLTLtoGNBA debug (intermediateFilesPath : String) (ltl2tgbaPath : String) timeout (ltl : LTL<'L>)  = 
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

            let res = Util.SystemCallUtil.systemCall ltl2tgbaPath args timeout

            match res with 
            | SystemCallSuccess _ -> 
                let c = File.ReadAllText(targetPath)
                HoaConversion.resultToGNBA c (fun x -> revDict.[x]) 
                |> Success
            | SystemCallTimeout -> 
                Timeout
            | SystemCallError err -> 
                Fail err
        with
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail ($"%s{e.Message}")

    let convertLTLtoNBA debug (intermediateFilesPath : String) (ltl2tgbaPath : String) timeout (ltl : LTL<'L>)  = 
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

            let res = Util.SystemCallUtil.systemCall ltl2tgbaPath args timeout

            match res with 
            | SystemCallSuccess _ -> 
                let c = File.ReadAllText(targetPath)
                HoaConversion.resultToNBA c (fun x -> revDict.[x]) 
                |> Success
            | SystemCallTimeout -> 
                Timeout
            | SystemCallError err -> 
                Fail err
        with
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail ($"%s{e.Message}")

    let convertLTLtoDPA debug (intermediateFilesPath : String) (ltl2tgbaPath : String) timeout (ltl : LTL<'L>)  = 
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

            let res = Util.SystemCallUtil.systemCall ltl2tgbaPath args timeout

            match res with 
            | SystemCallSuccess _ -> 
                let c = File.ReadAllText(targetPath)
                HoaConversion.resultToDPA c (fun x -> revDict.[x]) 
                |> Success  
            | SystemCallTimeout -> 
                Timeout
            | SystemCallError err -> 
                Fail err
        with
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail ($"%s{e.Message}")

module AutomataChecks = 
    let checkEmptiness debug (intermediateFilesPath : String) (autfiltPath : String) timeout (aut : AbstractAutomaton<int, 'L>) = 
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

            let res = Util.SystemCallUtil.systemCall autfiltPath args timeout

            match res with 
            | SystemCallSuccess c -> 
                if c = "" then false else true
                |> Success
            | SystemCallTimeout -> 
                Timeout
            | SystemCallError err -> 
                Fail err
        with
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail ($"%s{e.Message}")

    let checkContainment debug (intermediateFilesPath : String) (autfiltPath : String) timeout (aut1 : AbstractAutomaton<int, 'L>) (aut2 : AbstractAutomaton<int, 'L>)  = 
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
            let res = Util.SystemCallUtil.systemCall autfiltPath arg timeout

            match res with 
            | SystemCallSuccess c -> 
                if c = "" then false else true
                |> Success
            | SystemCallTimeout -> 
                Timeout
            | SystemCallError err -> 
                Fail err
        with
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail ($"%s{e.Message}")

    let checkEquivalence debug (intermediateFilesPath : String) (autfiltPath : String) timeout (aut1 : AbstractAutomaton<int, 'L>) (aut2 : AbstractAutomaton<int, 'L>) = 
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
            let res = Util.SystemCallUtil.systemCall autfiltPath arg timeout

            match res with 
            | SystemCallSuccess c -> 
                if c = "" then false else true
                |> Success
            | SystemCallTimeout -> 
                Timeout
            | SystemCallError err -> 
                Fail err
        with
        | _ when debug -> reraise() 
        | ConversionException err -> 
            Fail (err)
        | e -> 
            Fail ($"%s{e.Message}")
