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

module FsOmegaLib.NondeterminsticAutomatonSkeleton

open System 
open SAT 

open AutomatonSkeleton

exception private NotWellFormedException of String

// A AutomatonSkeleton which is specialized to non-deterministic automataon, i.e., no conjunction in the target of edges
type NondeterminsticAutomatonSkeleton<'T, 'L when 'T: comparison and 'L : comparison> = 
    {
        Skeleton : AutomatonSkeleton<'T, 'L>
    }

    member this.States = 
        this.Skeleton.States

    member this.Edges = 
        this.Skeleton.Edges
    
    member this.APs = 
        this.Skeleton.APs


module NondeterminsticAutomatonSkeleton = 

    let actuallyUsedAPs(skeleton : NondeterminsticAutomatonSkeleton<'T, 'L>) = 
        AutomatonSkeleton.actuallyUsedAPs skeleton.Skeleton


    let mapAPs (f : 'L -> 'U) (skeleton : NondeterminsticAutomatonSkeleton<'T, 'L>) = 
        {
            Skeleton = AutomatonSkeleton.mapAPs f skeleton.Skeleton
        }

    let mapStates (f : 'T -> 'S) (skeleton : NondeterminsticAutomatonSkeleton<'T, 'L>) = 
        {Skeleton = AutomatonSkeleton.mapStates f skeleton.Skeleton}
        
    let printBodyInHanoiFormat (stateStringer : 'T -> string) (accCondition : 'T -> string) (skeleton : NondeterminsticAutomatonSkeleton<'T, 'L>) = 
        AutomatonSkeleton.printBodyInHanoiFormat stateStringer accCondition skeleton.Skeleton

    let findError (skeleton : NondeterminsticAutomatonSkeleton<'T, 'L>) = 
        try 
            match AutomatonSkeleton.findError skeleton.Skeleton with 
            | Some err -> raise <| NotWellFormedException err 
            | None -> ()

            skeleton.Edges
            |> Map.values
            |> Seq.iter (fun x -> 
                x
                |> List.iter (fun (_, y) -> 
                    if Set.count y <> 1 then 
                        raise <| NotWellFormedException $"A conjunctive edge was used" 
                    )
                )

            None
        with 
        | NotWellFormedException msg -> Some msg
 
    let bringSkeletonsToSameAps (autList : list<NondeterminsticAutomatonSkeleton<'T, 'L>>) =
        autList
        |> List.map (fun x -> x.Skeleton)
        |> AutomatonSkeleton.bringSkeletonsToSameAps 
        |> List.map (fun x -> {Skeleton = x})



    let bringSkeletonPairToSameAps (skeleton1 : NondeterminsticAutomatonSkeleton<'T, 'L>) (skeleton2 : NondeterminsticAutomatonSkeleton<'U, 'L>) =
        let sk1, sk2 = AutomatonSkeleton.bringSkeletonPairToSameAps skeleton1.Skeleton skeleton2.Skeleton
        
        {Skeleton = sk1}, {Skeleton = sk2}
       

    let addAPsToSkeleton (aps : list<'L>)  (skeleton : NondeterminsticAutomatonSkeleton<'T, 'L>) =
        {
            Skeleton = AutomatonSkeleton.addAPsToSkeleton aps skeleton.Skeleton
        }
        
    let fixAPsToSkeleton (aps : list<'L>)  (skeleton : NondeterminsticAutomatonSkeleton<'T, 'L>) =
        {
            Skeleton = AutomatonSkeleton.fixAPsToSkeleton aps skeleton.Skeleton
        }

    let projectToTargetAPs (newAPs : list<'L>) (skeleton : NondeterminsticAutomatonSkeleton<int, 'L>)  = 
        {
            Skeleton = AutomatonSkeleton.projectToTargetAPs newAPs skeleton.Skeleton
        }
        