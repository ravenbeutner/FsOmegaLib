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

/// Module for nondetermintic safety automata, i.e., automata that accept all words, as long as there exists some run
module FsOmegaLib.NSA

open System
open System.IO

open SAT
open AutomatonSkeleton
open AbstractAutomaton

exception private NotWellFormedException of String

type NSA<'T, 'L when 'T : comparison and 'L : comparison> =
    {
        Skeleton : NondeterministicAutomatonSkeleton<'T, 'L>
        InitialStates : Set<'T>
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

                None
            with NotWellFormedException msg ->
                Some msg


        member this.ToHoaString (stateStringer : 'T -> String) (alphStringer : 'L -> String) =
            let s = new StringWriter()

            s.WriteLine("HOA: v1")

            s.WriteLine("States: " + string (this.States.Count))

            for n in this.InitialStates do
                s.WriteLine("Start: " + stateStringer (n))

            s.WriteLine(
                "AP: "
                + string (this.APs.Length)
                + " "
                + List.fold (fun s x -> s + " \"" + alphStringer (x) + "\"") "" this.APs
            )

            s.WriteLine("acc-name: all")

            s.WriteLine("Acceptance: 0 t")

            s.WriteLine "--BODY--"

            for n in this.States do
                let edges = this.Edges.[n]

                s.WriteLine("State: " + stateStringer (n))

                for (g, n') in edges do
                    s.WriteLine("[" + DNF.print g + "] " + stateStringer (n'))

            s.WriteLine "--END--"

            s.ToString()

module NSA =

    let actuallyUsedAPs (nsa : NSA<'T, 'L>) =
        NondeterministicAutomatonSkeleton.actuallyUsedAPs nsa.Skeleton

    let convertStatesToInt (nsa : NSA<'T, 'L>) =
        let idDict = nsa.Skeleton.States |> Seq.mapi (fun i x -> x, i) |> Map.ofSeq

        {
            NSA.Skeleton =
                {
                    AutomatonSkeleton.States = nsa.Skeleton.States |> Set.map (fun x -> idDict.[x])
                    APs = nsa.Skeleton.APs
                    Edges =
                        nsa.Skeleton.Edges
                        |> Map.toSeq
                        |> Seq.map (fun (k, v) -> idDict.[k], v |> List.map (fun (g, s) -> g, idDict.[s]))
                        |> Map.ofSeq
                }

            InitialStates = nsa.InitialStates |> Set.map (fun x -> idDict.[x])
        }

    let mapAPs (f : 'L -> 'U) (nsa : NSA<'T, 'L>) =
        {
            Skeleton = NondeterministicAutomatonSkeleton.mapAPs f nsa.Skeleton
            InitialStates = nsa.InitialStates
        }

    let trueAutomaton () : NSA<int, 'L> =
        {
            NSA.Skeleton =
                {
                    States = set ([ 0 ])
                    APs = []
                    Edges = [ 0, [ DNF.trueDNF, 0 ] ] |> Map.ofList
                }
            InitialStates = set ([ 0 ])
        }

    let falseAutomaton () : NSA<int, 'L> =
        {
            NSA.Skeleton =
                {
                    States = set ([ 0 ])
                    APs = []
                    Edges = [ 0, List.empty ] |> Map.ofList
                }
            InitialStates = set ([ 0 ])
        }

    let toHoaString (stateStringer : 'T -> String) (alphStringer : 'L -> String) (nsa : NSA<'T, 'L>) =
        (nsa :> AbstractAutomaton<'T, 'L>).ToHoaString stateStringer alphStringer

    let findError (nsa : NSA<'T, 'L>) =
        (nsa :> AbstractAutomaton<'T, 'L>).FindError()

    let bringToSameAPs (autList : list<NSA<'T, 'L>>) =
        autList
        |> List.map (fun x -> x.Skeleton)
        |> NondeterministicAutomatonSkeleton.bringSkeletonsToSameAps
        |> List.mapi (fun i x -> { autList.[i] with Skeleton = x })

    let bringPairToSameAPs (nsa1 : NSA<'T, 'L>) (nsa2 : NSA<'T, 'L>) =
        let sk1, sk2 =
            NondeterministicAutomatonSkeleton.bringSkeletonPairToSameAps nsa1.Skeleton nsa2.Skeleton

        { nsa1 with Skeleton = sk1 }, { nsa2 with Skeleton = sk2 }

    let addAPs (aps : list<'L>) (nsa : NSA<'T, 'L>) =
        { nsa with
            Skeleton = NondeterministicAutomatonSkeleton.addAPsToSkeleton aps nsa.Skeleton
        }

    let fixAPs (aps : list<'L>) (nsa : NSA<'T, 'L>) =
        { nsa with
            Skeleton = NondeterministicAutomatonSkeleton.fixAPsToSkeleton aps nsa.Skeleton
        }

    let projectToTargetAPs (newAPs : list<'L>) (nsa : NSA<int, 'L>) =
        { nsa with
            Skeleton = NondeterministicAutomatonSkeleton.projectToTargetAPs newAPs nsa.Skeleton
        }

    let computeBisimulationQuotient (nsa : NSA<int, 'L>) =
        let skeleton, m =
            NondeterministicAutomatonSkeleton.computeBisimulationQuotient (fun _ -> 0) nsa.Skeleton

        {
            NSA.Skeleton = skeleton
            InitialStates = nsa.InitialStates |> Set.map (fun x -> m.[x])
        }
