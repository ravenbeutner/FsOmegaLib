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

module FsOmegaLib.NBA

open System 
open System.IO

open SAT
open AutomatonSkeleton
open AbstractAutomaton

type NBA<'T, 'L when 'T: comparison and 'L : comparison> = 
    {
        Skeleton : AutomatonSkeleton<'T, 'L>
        InitialStates : Set<'T>
        AcceptingStates: Set<'T>
    }

    member this.States = 
        this.Skeleton.States

    member this.Edges = 
        this.Skeleton.Edges

    member this.APs = 
        this.Skeleton.APs

    interface AbstractAutomaton<'T, 'L> with
        member this.Skeleton = 
            this.Skeleton

        member this.ToHoaString (stateStringer : 'T -> String) (alphStringer : 'L -> String) =
            let s = new StringWriter() 

            s.WriteLine("HOA: v1")

            s.WriteLine ("States: " + string(this.States.Count))
            
            for n in this.InitialStates do 
                s.WriteLine ("Start: " + stateStringer(n))

            s.WriteLine ("AP: " + string(this.APs.Length) + " " + List.fold (fun s x -> s + " \"" + alphStringer(x) + "\"") "" this.APs)

            s.WriteLine ("acc-name: Buchi")
            s.WriteLine ("Acceptance: 1 Inf(0)")

            s.WriteLine "--BODY--"
            
            for n in this.States do 
                let edges = this.Edges.[n]

                let accString = 
                    if this.AcceptingStates.Contains n then 
                        "{0}"
                    else 
                        ""

                s.WriteLine("State: " + stateStringer(n) + " " + accString)

                for (g, n') in edges do 
                    s.WriteLine("[" + DNF.print g + "] " + stateStringer(n'))

            s.WriteLine "--END--"

            s.ToString() 

module NBA = 

    let actuallyUsedAPs(nba : NBA<'T, 'L>) = 
        AutomatonSkeleton.actuallyUsedAPs nba.Skeleton

    let convertStatesToInt (nba : NBA<'T, 'L>)  = 
        let idDict = 
            nba.Skeleton.States
            |> Seq.mapi (fun i x -> x, i)
            |> Map.ofSeq

        {
            NBA.Skeleton = 
                {
                    AutomatonSkeleton.States = 
                        nba.Skeleton.States
                        |> Set.map (fun x -> idDict.[x]);
                    APs = nba.Skeleton.APs;
                    Edges = 
                        nba.Skeleton.Edges 
                        |> Map.toSeq
                        |> Seq.map 
                            (fun (k, v) -> 
                                idDict.[k], v |> List.map (fun (g, s) -> g, idDict.[s])
                            )
                        |> Map.ofSeq;
                }

            InitialStates = 
                nba.InitialStates 
                |> Set.map (fun x -> idDict.[x]);

            AcceptingStates = 
                nba.AcceptingStates
                |> Set.map (fun x -> idDict.[x]);
        }
    
    let mapAPs (f : 'L -> 'U) (nba : NBA<'T, 'L>) = 
        {
            Skeleton = AutomatonSkeleton.mapAPs f nba.Skeleton
            InitialStates = nba.InitialStates
            AcceptingStates = nba.AcceptingStates
        }

    let trueAutomaton () : NBA<int, 'L> = 
        {
            NBA.Skeleton = {
                States = set([0])
                APs = []
                Edges = 
                    [0, [DNF.trueDNF, 0]]
                    |> Map.ofList
            }
            InitialStates = set([0])
            AcceptingStates = Set.singleton 0
        }

    let falseAutomaton () : NBA<int, 'L> = 
        {
            NBA.Skeleton = {
                States = set([0])
                APs = []
                Edges = 
                    [0, List.empty]
                    |> Map.ofList
            }
            InitialStates = set([0])
            AcceptingStates = Set.empty
        }

    let toHoaString (stateStringer : 'T -> String) (alphStringer : 'L -> String) (nba : NBA<'T, 'L>) = 
        (nba :> AbstractAutomaton<'T, 'L>).ToHoaString stateStringer alphStringer

    let bringToSameAPs (autList : list<NBA<'T, 'L>>) =
        autList
        |> List.map (fun x -> x.Skeleton)
        |> AutomatonSkeleton.bringSkeletonsToSameAps 
        |> List.mapi (fun i x -> 
            {autList.[i] with Skeleton = x}
            )

    let bringPairToSameAPs (gnba1 : NBA<'T, 'L>) (gnba2 : NBA<'U, 'L>) =
        let sk1, sk2 = AutomatonSkeleton.bringSkeletonPairToSameAps gnba1.Skeleton gnba2.Skeleton

        {gnba1 with Skeleton = sk1}, {gnba2 with Skeleton = sk2}


    let addAPs (aps : list<'L>)  (gnba : NBA<'T, 'L>) =
        {gnba with Skeleton = AutomatonSkeleton.addAPsToSkeleton aps gnba.Skeleton}

    let fixAPs (aps : list<'L>)  (gnba : NBA<'T, 'L>) =
        {gnba with Skeleton = AutomatonSkeleton.fixAPsToSkeleton aps gnba.Skeleton}

    let projectToTargetAPs (newAPs : list<'L>) (gnba : NBA<int, 'L>)  = 
        {gnba with Skeleton = AutomatonSkeleton.projectToTargetAPs newAPs gnba.Skeleton}
