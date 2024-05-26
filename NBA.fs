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

module FsOmegaLib.NBA

open System
open System.IO

open SAT
open AutomatonSkeleton
open AbstractAutomaton

exception private NotWellFormedException of String

type NBA<'T, 'L when 'T : comparison and 'L : comparison> =
    {
        Skeleton : NondeterministicAutomatonSkeleton<'T, 'L>
        InitialStates : Set<'T>
        AcceptingStates : Set<'T>
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
                |> Seq.iter (fun x ->
                    if this.Skeleton.States.Contains x |> not then
                        raise
                        <| NotWellFormedException $"State $A{x} is initial but not contained in the set of states"
                )

                this.AcceptingStates
                |> Seq.iter (fun x ->
                    if this.Skeleton.States.Contains x |> not then
                        raise
                        <| NotWellFormedException $"State $A{x} is accepting but not contained in the set of states"
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

            stringWriter.WriteLine("acc-name: Buchi")
            stringWriter.WriteLine("Acceptance: 1 Inf(0)")

            stringWriter.WriteLine "--BODY--"

            let accCondition s =
                if this.AcceptingStates.Contains s then "{0}" else ""

            stringWriter.WriteLine(
                NondeterministicAutomatonSkeleton.printBodyInHanoiFormat stateStringer accCondition this.Skeleton
            )

            stringWriter.WriteLine "--END--"

            stringWriter.ToString()


module NBA =

    let actuallyUsedAPs (nba : NBA<'T, 'L>) =
        NondeterministicAutomatonSkeleton.actuallyUsedAPs nba.Skeleton

    let convertStatesToInt (nba : NBA<'T, 'L>) =
        let idDict = nba.Skeleton.States |> Seq.mapi (fun i x -> x, i) |> Map.ofSeq

        {
            NBA.Skeleton =
                nba.Skeleton
                |> NondeterministicAutomatonSkeleton.mapStates (fun x -> idDict.[x])

            InitialStates = nba.InitialStates |> Set.map (fun x -> idDict.[x])

            AcceptingStates = nba.AcceptingStates |> Set.map (fun x -> idDict.[x])
        }

    let mapAPs (f : 'L -> 'U) (nba : NBA<'T, 'L>) =
        {
            Skeleton = NondeterministicAutomatonSkeleton.mapAPs f nba.Skeleton
            InitialStates = nba.InitialStates
            AcceptingStates = nba.AcceptingStates
        }

    let trueAutomaton () : NBA<int, 'L> =
        {
            NBA.Skeleton =
                {
                    AutomatonSkeleton.States = set ([ 0 ])
                    APs = []
                    Edges = [ 0, [ DNF.trueDNF, 0 ] ] |> Map.ofList
                }
            InitialStates = set ([ 0 ])
            AcceptingStates = Set.singleton 0
        }

    let falseAutomaton () : NBA<int, 'L> =
        {
            NBA.Skeleton =
                {
                    AutomatonSkeleton.States = set ([ 0 ])
                    APs = []
                    Edges = [ 0, List.empty ] |> Map.ofList
                }
            InitialStates = set ([ 0 ])
            AcceptingStates = Set.empty
        }

    let toHoaString (stateStringer : 'T -> String) (alphStringer : 'L -> String) (nba : NBA<'T, 'L>) =
        (nba :> AbstractAutomaton<'T, 'L>).ToHoaString stateStringer alphStringer

    let findError (nba : NBA<'T, 'L>) =
        (nba :> AbstractAutomaton<'T, 'L>).FindError()

    let bringToSameAPs (autList : list<NBA<'T, 'L>>) =
        autList
        |> List.map (fun x -> x.Skeleton)
        |> NondeterministicAutomatonSkeleton.bringSkeletonsToSameAps
        |> List.mapi (fun i x -> { autList.[i] with Skeleton = x })

    let bringPairToSameAPs (nba1 : NBA<'T, 'L>) (nba2 : NBA<'T, 'L>) =
        let sk1, sk2 =
            NondeterministicAutomatonSkeleton.bringSkeletonPairToSameAps nba1.Skeleton nba2.Skeleton

        { nba1 with Skeleton = sk1 }, { nba2 with Skeleton = sk2 }


    let addAPs (aps : list<'L>) (nba : NBA<'T, 'L>) =
        { nba with
            Skeleton = NondeterministicAutomatonSkeleton.addAPsToSkeleton aps nba.Skeleton
        }

    let fixAPs (aps : list<'L>) (nba : NBA<'T, 'L>) =
        { nba with
            Skeleton = NondeterministicAutomatonSkeleton.fixAPsToSkeleton aps nba.Skeleton
        }

    let projectToTargetAPs (newAPs : list<'L>) (nba : NBA<int, 'L>) =
        { nba with
            Skeleton = NondeterministicAutomatonSkeleton.projectToTargetAPs newAPs nba.Skeleton
        }

    let computeBisimulationQuotient (nba : NBA<int, 'L>) =
        let skeleton, m =
            NondeterministicAutomatonSkeleton.computeBisimulationQuotient
                (fun x -> Set.contains x nba.AcceptingStates)
                nba.Skeleton

        {
            NBA.Skeleton = skeleton
            InitialStates = nba.InitialStates |> Set.map (fun x -> m.[x])
            AcceptingStates = nba.AcceptingStates |> Set.map (fun x -> m.[x])
        }
