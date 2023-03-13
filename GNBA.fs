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

module FsOmegaLib.GNBA

open System 
open System.IO

open SAT
open AutomatonSkeleton
open AbstractAutomaton

exception private NotWellFormedException of String

type GNBA<'T, 'L when 'T: comparison and 'L : comparison> = 
    {
        Skeleton : AutomatonSkeleton<'T, 'L>
        InitialStates : Set<'T>
        AcceptanceSets: Map<'T, Set<int>>
        NumberOfAcceptingSets : int
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

        member this.FindError() = 
            try 
                match AutomatonSkeleton.findError this.Skeleton with 
                | Some err -> 
                    raise <| NotWellFormedException err 
                | None -> ()

                this.InitialStates
                |> Seq.iter (fun x -> 
                    if this.Skeleton.States.Contains x |> not then 
                        raise <| NotWellFormedException $"State $A{x} is initial but not contained in the set of states"
                )

                this.Skeleton.States
                |> Seq.iter (fun x -> 
                    if this.AcceptanceSets.ContainsKey x |> not then 
                        raise <| NotWellFormedException $"No acc-sets defined for state $A{x}"

                    this.AcceptanceSets.[x]
                    |> Set.iter (fun i -> 
                        if i >= this.NumberOfAcceptingSets || i < 0 then 
                            raise <| NotWellFormedException $"The accptance set %i{i} is used in state %A{x} but is out of range"
                        )
                )
                None 
            with 
            | NotWellFormedException msg -> Some msg


        member this.ToHoaString (stateStringer : 'T -> String) (alphStringer : 'L -> String) = 
            let s = new StringWriter() 

            s.WriteLine("HOA: v1")

            s.WriteLine ("States: " + string(this.States.Count))
            
            for n in this.InitialStates do 
                s.WriteLine ("Start: " + stateStringer(n))

            s.WriteLine ("AP: " + string(this.APs.Length) + " " + List.fold (fun s x -> s + " \"" + alphStringer(x) + "\"") "" this.APs)

            s.WriteLine ("acc-name: generalized-Buchi " + string(this.NumberOfAcceptingSets))

            let accString = 
                if this.NumberOfAcceptingSets = 0 then 
                    "t"
                else
                    [0..this.NumberOfAcceptingSets - 1]
                    |> List.map (fun i -> "Inf(" + string(i) + ")")
                    |> Util.combineStringsWithSeperator "&"
                

            s.WriteLine ("Acceptance: " + string(this.NumberOfAcceptingSets) + " " + accString)
            
            s.WriteLine "--BODY--"
            
            for n in this.States do 
                let edges = this.Edges.[n]
                let accSets = this.AcceptanceSets.[n]

                let accString = 
                    if accSets.Count = 0 then 
                        ""
                    else 
                        " {"
                        + 
                        (accSets
                        |> Seq.toList
                        |> List.map (fun x -> string x)
                        |> Util.combineStringsWithSeperator " ")
                        + 
                        "}"

                s.WriteLine("State: " + stateStringer(n) + " " + accString)

                for (g, n') in edges do 
                    s.WriteLine("[" + DNF.print g + "] " + stateStringer(n'))

            s.WriteLine "--END--"

            s.ToString()

module GNBA = 

    let actuallyUsedAPs(gnba : GNBA<'T, 'L>) = 
        AutomatonSkeleton.actuallyUsedAPs gnba.Skeleton

    let convertStatesToInt (gnba : GNBA<'T, 'L>)  = 
        let idDict = 
            gnba.Skeleton.States
            |> Seq.mapi (fun i x -> x, i)
            |> Map.ofSeq

        {
            GNBA.Skeleton = 
                {
                    AutomatonSkeleton.States = 
                        gnba.Skeleton.States
                        |> Set.map (fun x -> idDict.[x]);
                    APs = gnba.Skeleton.APs;
                    Edges = 
                        gnba.Skeleton.Edges 
                        |> Map.toSeq
                        |> Seq.map 
                            (fun (k, v) -> 
                                idDict.[k], v |> List.map (fun (g, s) -> g, idDict.[s])
                            )
                        |> Map.ofSeq;
                }

            InitialStates = 
                gnba.InitialStates 
                |> Set.map (fun x -> idDict.[x]);

            AcceptanceSets = 
                gnba.AcceptanceSets 
                |> Map.toSeq
                |> Seq.map 
                    (fun (k, v) -> 
                        idDict.[k], v
                    )
                |> Map.ofSeq;

            NumberOfAcceptingSets = 
                gnba.NumberOfAcceptingSets
        }
    
    let mapAPs (f : 'L -> 'U) (gnba : GNBA<'T, 'L>) = 
        {
            Skeleton = AutomatonSkeleton.mapAPs f gnba.Skeleton
            InitialStates = gnba.InitialStates
            AcceptanceSets = gnba.AcceptanceSets
            NumberOfAcceptingSets = gnba.NumberOfAcceptingSets
        }

    let trueAutomaton () : GNBA<int, 'L> = 
        {
            GNBA.Skeleton = {
                States = set([0])
                APs = []
                Edges = 
                    [0, [DNF.trueDNF, 0]]
                    |> Map.ofList
            }
            InitialStates = set([0])
            AcceptanceSets = 
                [0, Set.empty]
                |> Map.ofList
            NumberOfAcceptingSets = 0
        }

    let falseAutomaton () : GNBA<int, 'L> = 
        {
            GNBA.Skeleton = {
                States = set([0])
                APs = []
                Edges = 
                    [0, List.empty]
                    |> Map.ofList
            }
            InitialStates = set([0])
            AcceptanceSets = 
                [0, Set.empty]
                |> Map.ofList
            NumberOfAcceptingSets = 0
        }

    let toHoaString (stateStringer : 'T -> String) (alphStringer : 'L -> String) (gnba : GNBA<'T, 'L>) = 
        (gnba :> AbstractAutomaton<'T, 'L>).ToHoaString stateStringer alphStringer

    let findError (gnba : GNBA<'T, 'L>) = 
        (gnba :> AbstractAutomaton<'T, 'L>).FindError()

    let bringToSameAPs (autList : list<GNBA<'T, 'L>>) =
        autList
        |> List.map (fun x -> x.Skeleton)
        |> AutomatonSkeleton.bringSkeletonsToSameAps 
        |> List.mapi (fun i x -> 
            {autList.[i] with Skeleton = x}
            )

    let bringPairToSameAPs (gnba1 : GNBA<'T, 'L>) (gnba2 : GNBA<'U, 'L>) =
        let sk1, sk2 = AutomatonSkeleton.bringSkeletonPairToSameAps gnba1.Skeleton gnba2.Skeleton

        {gnba1 with Skeleton = sk1}, {gnba2 with Skeleton = sk2}

    let addAPs (aps : list<'L>)  (gnba : GNBA<'T, 'L>) =
        {gnba with Skeleton = AutomatonSkeleton.addAPsToSkeleton aps gnba.Skeleton}

    let fixAPs (aps : list<'L>)  (gnba : GNBA<'T, 'L>) =
        {gnba with Skeleton = AutomatonSkeleton.fixAPsToSkeleton aps gnba.Skeleton}

    let projectToTargetAPs (newAPs : list<'L>) (gnba : GNBA<int, 'L>)  = 
        {gnba with Skeleton = AutomatonSkeleton.projectToTargetAPs newAPs gnba.Skeleton}

