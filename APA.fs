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

module FsOmegaLib.APA


open System
open System.IO

open SAT
open AutomatonSkeleton
open AbstractAutomaton
open DPA
open NBA

exception private NotWellFormedException of String

type APA<'T, 'L when 'T : comparison and 'L : comparison> =
    {
        Skeleton : AlternatingAutomatonSkeleton<'T, 'L>
        InitialStates : Set<Set<'T>> // Disjunction of Conjunction
        Color : Map<'T, int>
    }

    member this.States = this.Skeleton.States

    member this.Edges = this.Skeleton.Edges

    member this.APs = this.Skeleton.APs

    interface AbstractAutomaton<'T, 'L> with
        member this.Skeleton = this.Skeleton

        member this.FindError() =
            try
                match AlternatingAutomatonSkeleton.findError this.Skeleton with
                | Some err -> raise <| NotWellFormedException err
                | None -> ()

                this.InitialStates
                |> Set.iter (
                    Set.iter (fun x ->
                        if this.Skeleton.States.Contains x |> not then
                            raise
                            <| NotWellFormedException $"The initial state %A{x} is not contained in the set of states"
                    )
                )

                this.Skeleton.States
                |> Seq.iter (fun x ->
                    if this.Color.ContainsKey x |> not then
                        raise <| NotWellFormedException $"No color defined for state $A{x}"
                )

                None
            with NotWellFormedException msg ->
                Some msg

        member this.ToHoaString (stateStringer : 'T -> String) (alphStringer : 'L -> String) =
            let stringWriter = new StringWriter()

            stringWriter.WriteLine("HOA: v1")

            stringWriter.WriteLine("States: " + string this.States.Count)

            for s in this.InitialStates do
                let c = s |> Set.toList |> List.map stateStringer |> String.concat " & "

                stringWriter.WriteLine("Start: " + c)

            let apsString =
                this.APs
                |> List.map (fun x -> "\"" + alphStringer (x) + "\"")
                |> String.concat " "

            stringWriter.WriteLine("AP: " + string (this.APs.Length) + " " + apsString)

            let rec createParityString c =
                if c = 0 then
                    "Inf(0)"
                else if c % 2 = 0 then
                    "(Inf(" + string (c) + ") | " + createParityString (c - 1) + ")"
                else
                    "(Fin(" + string (c) + ") & " + createParityString (c - 1) + ")"

            let maxColour = this.Color |> Map.toSeq |> Seq.map snd |> Seq.max

            stringWriter.WriteLine("acc-name: parity max even " + string (maxColour + 1))
            stringWriter.WriteLine("Acceptance: " + string (maxColour + 1) + " " + createParityString maxColour)

            stringWriter.WriteLine "--BODY--"

            let accCondition s = "{" + string this.Color.[s] + "}"

            stringWriter.WriteLine(
                AlternatingAutomatonSkeleton.printBodyInHanoiFormat stateStringer accCondition this.Skeleton
            )

            stringWriter.WriteLine "--END--"

            stringWriter.ToString()


module APA =
    let actuallyUsedAPs (apa : APA<'T, 'L>) =
        AlternatingAutomatonSkeleton.actuallyUsedAPs apa.Skeleton

    let convertStatesToInt (apa : APA<'T, 'L>) =
        let idDict = apa.Skeleton.States |> Seq.mapi (fun i x -> x, i) |> Map.ofSeq

        {
            APA.Skeleton = apa.Skeleton |> AlternatingAutomatonSkeleton.mapStates (fun x -> idDict.[x])

            InitialStates = apa.InitialStates |> Set.map (Set.map (fun x -> idDict.[x]))

            Color = apa.Color |> Map.toSeq |> Seq.map (fun (k, v) -> idDict.[k], v) |> Map.ofSeq
        }

    let fromDPA (dpa : DPA<'T, 'L>) =
        {
            APA.Skeleton = dpa.Skeleton |> NondeterministicAutomatonSkeleton.toAlternatingAutomatonSkeleton
            InitialStates = dpa.InitialState |> Set.singleton |> Set.singleton
            Color = dpa.Color
        }

    let fromNBA (nba : NBA<'T, 'L>) =
        {
            APA.Skeleton = nba.Skeleton |> NondeterministicAutomatonSkeleton.toAlternatingAutomatonSkeleton
            InitialStates = nba.InitialStates |> Set.singleton
            Color =
                nba.States
                |> Seq.map (fun x -> x, (if nba.AcceptingStates.Contains x then 2 else 1))
                |> Map.ofSeq
        }

    let mapAPs (f : 'L -> 'U) (apa : APA<'T, 'L>) =
        {
            Skeleton = AlternatingAutomatonSkeleton.mapAPs f apa.Skeleton
            InitialStates = apa.InitialStates
            Color = apa.Color
        }

    let trueAutomaton () : APA<int, 'L> =
        {
            APA.Skeleton =
                {
                    AlternatingAutomatonSkeleton.States = set ([ 0 ])
                    APs = []
                    Edges = [ 0, [ DNF.trueDNF, Set.singleton 0 ] ] |> Map.ofList
                }
            InitialStates = Set.singleton (Set.singleton 0)
            Color = [ (0, 0) ] |> Map.ofList
        }

    let falseAutomaton () : APA<int, 'L> =
        {
            APA.Skeleton =
                {
                    States = set ([ 0 ])
                    APs = []
                    Edges = [ 0, List.empty ] |> Map.ofList
                }
            InitialStates = Set.singleton (Set.singleton 0)
            Color = [ (0, 1) ] |> Map.ofList
        }

    let toHoaString (stateStringer : 'T -> String) (alphStringer : 'L -> String) (apa : APA<'T, 'L>) =
        (apa :> AbstractAutomaton<'T, 'L>).ToHoaString stateStringer alphStringer

    let findError (apa : APA<'T, 'L>) =
        (apa :> AbstractAutomaton<'T, 'L>).FindError()

    let bringToSameAPs (autList : list<APA<'T, 'L>>) =
        autList
        |> List.map (fun x -> x.Skeleton)
        |> AlternatingAutomatonSkeleton.bringSkeletonsToSameAps
        |> List.mapi (fun i x -> { autList.[i] with Skeleton = x })

    let bringPairToSameAPs (apa1 : APA<'T, 'L>) (apa2 : APA<'T, 'L>) =
        let sk1, sk2 =
            AlternatingAutomatonSkeleton.bringSkeletonPairToSameAps apa1.Skeleton apa2.Skeleton

        { apa1 with Skeleton = sk1 }, { apa2 with Skeleton = sk2 }

    let addAPs (aps : list<'L>) (apa : APA<'T, 'L>) =
        { apa with
            Skeleton = AlternatingAutomatonSkeleton.addAPsToSkeleton aps apa.Skeleton
        }

    let fixAPs (aps : list<'L>) (apa : APA<'T, 'L>) =
        { apa with
            Skeleton = AlternatingAutomatonSkeleton.fixAPsToSkeleton aps apa.Skeleton
        }

    let projectToTargetAPs (newAPs : list<'L>) (apa : APA<'T, 'L>) =
        { apa with
            Skeleton = AlternatingAutomatonSkeleton.projectToTargetAPs newAPs apa.Skeleton
        }

    let computeBisimulationQuotient (apa : APA<'T, 'L>) =
        let bisimSkeleton, m =
            AutomatonSkeleton.AlternatingAutomatonSkeleton.computeBisimulationQuotient
                (fun x -> apa.Color.[x])
                apa.Skeleton

        {
            APA.Skeleton = bisimSkeleton
            InitialStates = apa.InitialStates |> Set.map (Set.map (fun x -> m.[x]))
            Color =
                bisimSkeleton.States
                |> Seq.map (fun x ->
                    let s = m |> Map.toSeq |> Seq.find (fun (_, y) -> x = y) |> fst
                    x, apa.Color.[s]
                )
                |> Map.ofSeq
        }
