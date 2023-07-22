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

module FsOmegaLib.DPA

open System 
open System.IO

open SAT
open NondeterminsticAutomatonSkeleton
open AbstractAutomaton

exception private NotWellFormedException of String
type DPA<'T, 'L when 'T: comparison and 'L : comparison> = 
    {
        Skeleton : NondeterminsticAutomatonSkeleton<'T, 'L>
        InitialState : 'T
        Color : Map<'T, int>
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

                if this.Skeleton.States.Contains this.InitialState |> not then 
                    raise <| NotWellFormedException $"The initial state is not contained in the set of states"
                
                this.Skeleton.States
                |> Seq.iter (fun x -> 
                    if this.Color.ContainsKey x |> not then 
                        raise <| NotWellFormedException $"No color defined for state $A{x}"
                )
                
                None 
            with 
            | NotWellFormedException msg -> Some msg

        member this.ToHoaString (stateStringer : 'T -> String) (alphStringer : 'L -> String) =
            let stringWriter = new StringWriter() 

            stringWriter.WriteLine("HOA: v1")

            stringWriter.WriteLine ("States: " + string this.States.Count)
            
            stringWriter.WriteLine ("Start: " + stateStringer this.InitialState)

            let apsString = 
                this.APs 
                |> List.map (fun x -> "\"" + alphStringer(x) + "\"") 
                |> Util.combineStringsWithSeperator " "

            stringWriter.WriteLine ("AP: " + string(this.APs.Length) + " " + apsString)
             
            let rec createParityString c = 
                if c = 0 then 
                    "Inf(0)"
                else 
                    if c % 2 = 0 then 
                        "(Inf(" + string(c) + ") | " + createParityString(c-1) + ")"
                    else
                        "(Fin(" + string(c) + ") & " + createParityString(c-1) + ")"

            let maxColour = 
                this.Color |> Map.toSeq |> Seq.map snd |> Seq.max

            stringWriter.WriteLine ("acc-name: parity max even " + string(maxColour + 1))
            stringWriter.WriteLine ("Acceptance: " + string(maxColour + 1) + " " + createParityString maxColour)
            
            stringWriter.WriteLine "--BODY--"

            let accCondition s = 
                "{" + string this.Color.[s] + "}"

            stringWriter.WriteLine (NondeterminsticAutomatonSkeleton.printBodyInHanoiFormat stateStringer accCondition this.Skeleton)
            
            stringWriter.WriteLine "--END--"

            stringWriter.ToString()
            
module DPA = 
    let actuallyUsedAPs(dpa : DPA<'T, 'L>) = 
        NondeterminsticAutomatonSkeleton.actuallyUsedAPs dpa.Skeleton

    let convertStatesToInt (dpa : DPA<'T, 'L>)  = 
        let idDict = 
            dpa.Skeleton.States
            |> Seq.mapi (fun i x -> x, i)
            |> Map.ofSeq

        {
            DPA.Skeleton = 
                dpa.Skeleton
                |> NondeterminsticAutomatonSkeleton.mapStates (fun x -> idDict.[x])

            InitialState = idDict.[dpa.InitialState];

            Color = 
                dpa.Color
                |> Map.toSeq
                |> Seq.map (fun (k, v) -> idDict.[k], v)
                |> Map.ofSeq;
        }
    
    let mapAPs (f : 'L -> 'U) (dpa : DPA<'T, 'L>) = 
        {
            Skeleton = NondeterminsticAutomatonSkeleton.mapAPs f dpa.Skeleton
            InitialState = dpa.InitialState
            Color = dpa.Color
        }

    let trueAutomaton () : DPA<int, 'L> = 
        {
            DPA.Skeleton = {
                NondeterminsticAutomatonSkeleton.Skeleton = 
                    {
                        States = set([0])
                        APs = []
                        Edges = 
                            [0, [DNF.trueDNF, Set.singleton 0]]
                            |> Map.ofList
                    }
            }
            InitialState = 0
            Color = [0, 0] |> Map.ofList
        }

    let falseAutomaton () : DPA<int, 'L> = 
        {
            DPA.Skeleton = {
                NondeterminsticAutomatonSkeleton.Skeleton = 
                    {
                        States = set([0])
                        APs = []
                        Edges = 
                            [0, List.empty]
                            |> Map.ofList
                    }
            }
            InitialState = 0
            Color = [0, 1] |> Map.ofList
        }

    let toHoaString (stateStringer : 'T -> String) (alphStringer : 'L -> String) (dpa : DPA<'T, 'L>) = 
        (dpa :> AbstractAutomaton<'T, 'L>).ToHoaString stateStringer alphStringer

    let findError (dpa : DPA<'T, 'L>) = 
        (dpa :> AbstractAutomaton<'T, 'L>).FindError()

    let bringToSameAPs (autList : list<DPA<'T, 'L>>) =
        autList
        |> List.map (fun x -> x.Skeleton)
        |> NondeterminsticAutomatonSkeleton.bringSkeletonsToSameAps 
        |> List.mapi (fun i x -> 
            {autList.[i] with Skeleton = x}
            )

    let bringPairToSameAPs (dpa1 : DPA<'T, 'L>) (dpa2 : DPA<'U, 'L>) =
        let sk1, sk2 = NondeterminsticAutomatonSkeleton.bringSkeletonPairToSameAps dpa1.Skeleton dpa2.Skeleton

        {dpa1 with Skeleton = sk1}, {dpa2 with Skeleton = sk2}

    let addAPs (aps : list<'L>)  (dpa : DPA<'T, 'L>) =
        {dpa with Skeleton = NondeterminsticAutomatonSkeleton.addAPsToSkeleton aps dpa.Skeleton}

    let fixAPs (aps : list<'L>)  (dpa : DPA<'T, 'L>) =
        {dpa with Skeleton = NondeterminsticAutomatonSkeleton.fixAPsToSkeleton aps dpa.Skeleton}

    let projectToTargetAPs (newAPs : list<'L>) (dpa : DPA<int, 'L>)  = 
        {dpa with Skeleton = NondeterminsticAutomatonSkeleton.projectToTargetAPs newAPs dpa.Skeleton}
