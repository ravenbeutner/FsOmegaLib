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
open NondeterminsticAutomatonSkeleton
open AbstractAutomaton

exception private NotWellFormedException of String

type NBA<'T, 'L when 'T: comparison and 'L : comparison> = 
    {
        Skeleton : NondeterminsticAutomatonSkeleton<'T, 'L>
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
            this.Skeleton.Skeleton

        member this.FindError() = 
            try 
                match NondeterminsticAutomatonSkeleton.findError this.Skeleton with 
                | Some err -> 
                    raise <| NotWellFormedException err 
                | None -> ()

                this.InitialStates
                |> Seq.iter (fun x -> 
                    if this.Skeleton.States.Contains x |> not then 
                        raise <| NotWellFormedException $"State $A{x} is initial but not contained in the set of states"
                )

                this.AcceptingStates
                |> Seq.iter (fun x -> 
                    if this.Skeleton.States.Contains x |> not then 
                        raise <| NotWellFormedException $"State $A{x} is accepting but not contained in the set of states"
                )

                None 
            with 
            | NotWellFormedException msg -> Some msg

        member this.ToHoaString (stateStringer : 'T -> String) (alphStringer : 'L -> String) =
            let stringWriter = new StringWriter() 

            stringWriter.WriteLine("HOA: v1")

            stringWriter.WriteLine ("States: " + string this.States.Count)
            
            for s in this.InitialStates do 
                stringWriter.WriteLine ("Start: " + stateStringer s)

            let apsString = 
                this.APs 
                |> List.map (fun x -> "\"" + alphStringer(x) + "\"") 
                |> Util.combineStringsWithSeperator " "

            stringWriter.WriteLine ("AP: " + string(this.APs.Length) + " " + apsString)
             
            stringWriter.WriteLine ("acc-name: Buchi")
            stringWriter.WriteLine ("Acceptance: 1 Inf(0)")
            
            stringWriter.WriteLine "--BODY--"

            let accCondition s = 
                if this.AcceptingStates.Contains s then 
                    "{0}"
                else 
                    ""

            stringWriter.WriteLine (NondeterminsticAutomatonSkeleton.printBodyInHanoiFormat stateStringer accCondition this.Skeleton)
            
            stringWriter.WriteLine "--END--"

            stringWriter.ToString()


module NBA = 

    let actuallyUsedAPs(nba : NBA<'T, 'L>) = 
        NondeterminsticAutomatonSkeleton.actuallyUsedAPs nba.Skeleton

    let convertStatesToInt (nba : NBA<'T, 'L>)  = 
        let idDict = 
            nba.Skeleton.States
            |> Seq.mapi (fun i x -> x, i)
            |> Map.ofSeq

        {
            NBA.Skeleton =
                nba.Skeleton
                |> NondeterminsticAutomatonSkeleton.mapStates (fun x -> idDict.[x])

            InitialStates = 
                nba.InitialStates 
                |> Set.map (fun x -> idDict.[x]);

            AcceptingStates = 
                nba.AcceptingStates
                |> Set.map (fun x -> idDict.[x]);
        }
    
    let mapAPs (f : 'L -> 'U) (nba : NBA<'T, 'L>) = 
        {
            Skeleton = NondeterminsticAutomatonSkeleton.mapAPs f nba.Skeleton
            InitialStates = nba.InitialStates
            AcceptingStates = nba.AcceptingStates
        }

    let trueAutomaton () : NBA<int, 'L> = 
        {
            NBA.Skeleton = {
                NondeterminsticAutomatonSkeleton.Skeleton = 
                    {
                        States = set([0])
                        APs = []
                        Edges = 
                            [0, [DNF.trueDNF, Set.singleton 0]]
                            |> Map.ofList
                    }
            }
            InitialStates = set([0])
            AcceptingStates = Set.singleton 0
        }

    let falseAutomaton () : NBA<int, 'L> = 
        {
            NBA.Skeleton = {
                NondeterminsticAutomatonSkeleton.Skeleton = 
                    {
                        States = set([0])
                        APs = []
                        Edges = 
                            [0, List.empty]
                            |> Map.ofList
                    }
            }
            InitialStates = set([0])
            AcceptingStates = Set.empty
        }

    let toHoaString (stateStringer : 'T -> String) (alphStringer : 'L -> String) (nba : NBA<'T, 'L>) = 
        (nba :> AbstractAutomaton<'T, 'L>).ToHoaString stateStringer alphStringer

    let findError (nba : NBA<'T, 'L>) = 
        (nba :> AbstractAutomaton<'T, 'L>).FindError()

    let bringToSameAPs (autList : list<NBA<'T, 'L>>) =
        autList
        |> List.map (fun x -> x.Skeleton)
        |> NondeterminsticAutomatonSkeleton.bringSkeletonsToSameAps 
        |> List.mapi (fun i x -> 
            {autList.[i] with Skeleton = x}
            )

    let bringPairToSameAPs (gnba1 : NBA<'T, 'L>) (gnba2 : NBA<'U, 'L>) =
        let sk1, sk2 = NondeterminsticAutomatonSkeleton.bringSkeletonPairToSameAps gnba1.Skeleton gnba2.Skeleton

        {gnba1 with Skeleton = sk1}, {gnba2 with Skeleton = sk2}


    let addAPs (aps : list<'L>)  (gnba : NBA<'T, 'L>) =
        {gnba with Skeleton = NondeterminsticAutomatonSkeleton.addAPsToSkeleton aps gnba.Skeleton}

    let fixAPs (aps : list<'L>)  (gnba : NBA<'T, 'L>) =
        {gnba with Skeleton = NondeterminsticAutomatonSkeleton.fixAPsToSkeleton aps gnba.Skeleton}

    let projectToTargetAPs (newAPs : list<'L>) (gnba : NBA<int, 'L>)  = 
        {gnba with Skeleton = NondeterminsticAutomatonSkeleton.projectToTargetAPs newAPs gnba.Skeleton}
