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

module FsOmegaLib.NPA

open System
open System.IO

open SAT
open AutomatonSkeleton
open AbstractAutomaton

exception private NotWellFormedException of String

type NPA<'T, 'L when 'T : comparison and 'L : comparison> =
    {
        Skeleton : NondeterministicAutomatonSkeleton<'T, 'L>
        InitialStates : Set<'T>
        Color : Map<'T, int>
    }

    member this.States = this.Skeleton.States

    member this.Edges = this.Skeleton.Edges

    member this.APs = this.Skeleton.APs

    interface AbstractAutomaton<'T, 'L> with
        member this.Skeleton =
            NondeterministicAutomatonSkeleton.toAlternatingAutomatonSkeleton this.Skeleton

        member this.FindError() =
            try
                match NondeterministicAutomatonSkeleton.findError this.Skeleton with
                | Some err -> raise <| NotWellFormedException err
                | None -> ()

                this.InitialStates
                |> Set.iter (fun x ->
                    if this.Skeleton.States.Contains x |> not then
                        raise
                        <| NotWellFormedException $"The initial state %A{x} is not contained in the set of states"
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
                stringWriter.WriteLine("Start: " + stateStringer s)

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
                NondeterministicAutomatonSkeleton.printBodyInHanoiFormat stateStringer accCondition this.Skeleton
            )

            stringWriter.WriteLine "--END--"

            stringWriter.ToString()

module NPA =
    let actuallyUsedAPs (npa : NPA<'T, 'L>) =
        NondeterministicAutomatonSkeleton.actuallyUsedAPs npa.Skeleton

    let convertStatesToInt (npa : NPA<'T, 'L>) =
        let idDict = npa.Skeleton.States |> Seq.mapi (fun i x -> x, i) |> Map.ofSeq

        {
            NPA.Skeleton =
                npa.Skeleton
                |> NondeterministicAutomatonSkeleton.mapStates (fun x -> idDict.[x])

            InitialStates = npa.InitialStates |> Set.map (fun x -> idDict.[x])

            Color = npa.Color |> Map.toSeq |> Seq.map (fun (k, v) -> idDict.[k], v) |> Map.ofSeq
        }

    let mapAPs (f : 'L -> 'U) (npa : NPA<'T, 'L>) =
        {
            Skeleton = NondeterministicAutomatonSkeleton.mapAPs f npa.Skeleton
            InitialStates = npa.InitialStates
            Color = npa.Color
        }

    let trueAutomaton () : NPA<int, 'L> =
        {
            NPA.Skeleton =
                {
                    AutomatonSkeleton.States = set ([ 0 ])
                    APs = []
                    Edges = [ 0, [ DNF.trueDNF, 0 ] ] |> Map.ofList
                }
            InitialStates = Set.singleton 0
            Color = [ 0, 0 ] |> Map.ofList
        }

    let falseAutomaton () : NPA<int, 'L> =
        {
            NPA.Skeleton =
                {
                    AutomatonSkeleton.States = set ([ 0 ])
                    APs = []
                    Edges = [ 0, List.empty ] |> Map.ofList
                }
            InitialStates = Set.singleton 0
            Color = [ 0, 1 ] |> Map.ofList
        }

    let toHoaString (stateStringer : 'T -> String) (alphStringer : 'L -> String) (npa : NPA<'T, 'L>) =
        (npa :> AbstractAutomaton<'T, 'L>).ToHoaString stateStringer alphStringer

    let findError (npa : NPA<'T, 'L>) =
        (npa :> AbstractAutomaton<'T, 'L>).FindError()

    let bringToSameAPs (autList : list<NPA<'T, 'L>>) =
        autList
        |> List.map (fun x -> x.Skeleton)
        |> NondeterministicAutomatonSkeleton.bringSkeletonsToSameAps
        |> List.mapi (fun i x -> { autList.[i] with Skeleton = x })

    let bringPairToSameAPs (npa1 : NPA<'T, 'L>) (npa2 : NPA<'T, 'L>) =
        let sk1, sk2 =
            NondeterministicAutomatonSkeleton.bringSkeletonPairToSameAps npa1.Skeleton npa2.Skeleton

        { npa1 with Skeleton = sk1 }, { npa2 with Skeleton = sk2 }

    let addAPs (aps : list<'L>) (npa : NPA<'T, 'L>) =
        { npa with
            Skeleton = NondeterministicAutomatonSkeleton.addAPsToSkeleton aps npa.Skeleton
        }

    let fixAPs (aps : list<'L>) (npa : NPA<'T, 'L>) =
        { npa with
            Skeleton = NondeterministicAutomatonSkeleton.fixAPsToSkeleton aps npa.Skeleton
        }

    let projectToTargetAPs (newAPs : list<'L>) (npa : NPA<int, 'L>) =
        { npa with
            Skeleton = NondeterministicAutomatonSkeleton.projectToTargetAPs newAPs npa.Skeleton
        }

    let computeBisimulationQuotient (npa : NPA<int, 'L>) =
        let skeleton, m =
            NondeterministicAutomatonSkeleton.computeBisimulationQuotient (fun x -> npa.Color.[x]) npa.Skeleton

        {
            NPA.Skeleton = skeleton
            InitialStates = npa.InitialStates |> Set.map (fun x -> m.[x])
            Color = npa.Color |> Map.toSeq |> Seq.map (fun (s, c) -> m.[s], c) |> Map.ofSeq
        }
