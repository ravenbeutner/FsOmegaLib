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

module FsOmegaLib.AutomatonSkeleton

open System
open System.IO

open SAT

exception private NotWellFormedException of String

type AutomatonSkeleton<'T, 'L, 'G when 'T : comparison and 'L : comparison> =
    {
        States : Set<'T>
        APs : list<'L>
        Edges : Map<'T, list<DNF<int> * 'G>>
    } // The type 'G will either be 'T (representing a non-determinstic automaton) or Set<'T> (representing an alternating automaton)

// The target of each edge is a set of states, representing a conjunction over all those states
type AlternatingAutomatonSkeleton<'T, 'L when 'T : comparison and 'L : comparison> = AutomatonSkeleton<'T, 'L, Set<'T>>


// The target of each edge is a single state
type NondeterministicAutomatonSkeleton<'T, 'L when 'T : comparison and 'L : comparison> = AutomatonSkeleton<'T, 'L, 'T>


module private AutomatonSkeleton =

    let actuallyUsedAPs (skeleton : AutomatonSkeleton<'T, 'L, 'G>) =
        skeleton.Edges
        |> Seq.map (fun x -> x.Value |> List.map ((fun (g, _) -> DNF.atoms g)) |> Set.unionMany)
        |> Set.unionMany
        |> Set.map (fun i -> skeleton.APs.[i])


    let mapAPs (f : 'L -> 'U) (skeleton : AutomatonSkeleton<'T, 'L, 'G>) =
        {
            AutomatonSkeleton.States = skeleton.States
            APs = skeleton.APs |> List.map f
            Edges = skeleton.Edges
        }

    let mapStates (f : 'T -> 'S) (h : 'G -> 'V) (skeleton : AutomatonSkeleton<'T, 'L, 'G>) =
        {
            AutomatonSkeleton.States = skeleton.States |> Set.map f
            APs = skeleton.APs
            Edges =
                skeleton.Edges
                |> Map.toSeq
                |> Seq.map (fun (s, e) -> f s, e |> List.map (fun (g, sucs) -> g, h sucs))
                |> Map.ofSeq
        }

    let printBodyInHanoiFormat
        (stateStringer : 'T -> string)
        (accConditionStringer : 'T -> string)
        (sucStringer : 'G -> string)
        (skeleton : AutomatonSkeleton<'T, 'L, 'G>)
        =
        skeleton.States
        |> Set.toList
        |> List.map (fun s ->
            let edgesStr =
                skeleton.Edges.[s]
                |> List.map (fun (g, s') ->
                    let sucStatesStr = sucStringer s'
                    "[" + DNF.print g + "] " + sucStatesStr
                )
                |> String.concat "\n"

            "State: " + stateStringer s + " " + accConditionStringer s + "\n" + edgesStr
        )
        |> String.concat "\n"

    let bringSkeletonsToSameAps (autList : list<AutomatonSkeleton<'T, 'L, 'G>>) =
        let combinedAps =
            autList |> List.map (fun x -> x.APs) |> List.concat |> List.distinct

        let remapSkeleton (skeleton : AutomatonSkeleton<'T, 'L, 'G>) =
            let apAlignment i =
                List.findIndex ((=) skeleton.APs.[i]) combinedAps

            { skeleton with
                APs = combinedAps
                Edges =
                    skeleton.Edges
                    |> Map.map (fun _ e -> e |> List.map (fun (g, s) -> DNF.map apAlignment g, s))
            }

        autList |> List.map remapSkeleton

    let bringSkeletonPairToSameAps
        (skeleton1 : AutomatonSkeleton<'T, 'L, 'G>)
        (skeleton2 : AutomatonSkeleton<'U, 'L, 'G>)
        =
        let combinedAps = List.append skeleton1.APs skeleton2.APs |> List.distinct

        let remapSkeleton (skeleton : AutomatonSkeleton<'X, 'L, 'G>) =
            let apAlignment i =
                List.findIndex ((=) skeleton.APs.[i]) combinedAps

            { skeleton with
                APs = combinedAps
                Edges =
                    skeleton.Edges
                    |> Map.map (fun _ e -> e |> List.map (fun (g, s) -> DNF.map apAlignment g, s))
            }

        remapSkeleton skeleton1, remapSkeleton skeleton2

    let addAPsToSkeleton (aps : list<'L>) (skeleton : AutomatonSkeleton<'T, 'L, 'G>) =
        let combinedAps = List.append skeleton.APs aps |> List.distinct

        let remapSkeleton (skeleton : AutomatonSkeleton<'X, 'L, 'G>) =
            let apAlignment i =
                List.findIndex ((=) skeleton.APs.[i]) combinedAps

            { skeleton with
                APs = combinedAps
                Edges =
                    skeleton.Edges
                    |> Map.map (fun _ e -> e |> List.map (fun (g, s) -> DNF.map apAlignment g, s))
            }

        remapSkeleton skeleton

    let fixAPsToSkeleton (aps : list<'L>) (skeleton : AutomatonSkeleton<'T, 'L, 'G>) =
        skeleton.APs
        |> List.iter (fun x ->
            if List.contains x aps |> not then
                raise <| Exception($"%A{x} was not contained in the APs to be fixed")

            ()
        )

        let remapSkeleton (skeleton : AutomatonSkeleton<'X, 'L, 'G>) =
            let apAlignment i =
                List.findIndex ((=) skeleton.APs.[i]) aps

            { skeleton with
                APs = aps
                Edges =
                    skeleton.Edges
                    |> Map.map (fun _ e -> e |> List.map (fun (g, s) -> DNF.map apAlignment g, s))
            }

        remapSkeleton skeleton

    let projectToTargetAPs (newAPs : list<'L>) (skeleton : AutomatonSkeleton<'T, 'L, 'G>) =

        let apRemapping =
            newAPs
            |> List.mapi (fun i x -> List.findIndex ((=) x) skeleton.APs, i)
            |> Map.ofList

        let projectedAPsIndices =
            skeleton.APs
            |> List.indexed
            |> List.filter (fun (_, x) -> List.contains x newAPs |> not)
            |> List.map fst
            |> set

        {
            AutomatonSkeleton.States = skeleton.States
            APs = newAPs
            Edges =
                skeleton.Edges
                |> Map.map (fun _ x ->
                    x
                    |> List.map (fun (g, t) ->
                        let newGuard =
                            g
                            |> DNF.existentialProjection projectedAPsIndices
                            |> DNF.map (fun x -> apRemapping.[x])

                        newGuard, t
                    )
                )
        }



module AlternatingAutomatonSkeleton =

    let actuallyUsedAPs (skeleton : AlternatingAutomatonSkeleton<'T, 'L>) =
        AutomatonSkeleton.actuallyUsedAPs skeleton

    let mapAPs (f : 'L -> 'U) (skeleton : AlternatingAutomatonSkeleton<'T, 'L>) = AutomatonSkeleton.mapAPs f skeleton

    let mapStates (f : 'T -> 'S) (skeleton : AlternatingAutomatonSkeleton<'T, 'L>) =
        AutomatonSkeleton.mapStates f (fun (x : Set<'T>) -> Set.map f x) skeleton

    let printBodyInHanoiFormat
        (stateStringer : 'T -> string)
        (accConditionStringer : 'T -> string)
        (skeleton : AlternatingAutomatonSkeleton<'T, 'L>)
        =
        let conjunctionStringer s =
            s |> Set.toList |> List.map stateStringer |> String.concat " & "


        AutomatonSkeleton.printBodyInHanoiFormat stateStringer accConditionStringer conjunctionStringer skeleton

    let findError (skeleton : AlternatingAutomatonSkeleton<'T, 'L>) =
        try
            skeleton.States
            |> Seq.iter (fun x ->
                if skeleton.Edges.ContainsKey x |> not then
                    raise <| NotWellFormedException $"No edges defined for state $A{x}"

                skeleton.Edges.[x]
                |> List.iter (fun (g, t) ->
                    t
                    |> Set.iter (fun s ->
                        if skeleton.States.Contains s |> not then
                            raise
                            <| NotWellFormedException
                                $"State $A{s} is a conjunctive successor of states %A{x} but not defined as a state"
                    )

                    g
                    |> DNF.atoms
                    |> Set.iter (fun i ->
                        if i >= skeleton.APs.Length || i < 0 then
                            raise
                            <| NotWellFormedException
                                $"A transition guard from state $A{x} to %A{t} indexed to AP-index %i{i} which is out of range"
                    )
                )
            )

            None
        with NotWellFormedException msg ->
            Some msg

    let bringSkeletonsToSameAps (autList : list<AlternatingAutomatonSkeleton<'T, 'L>>) =
        AutomatonSkeleton.bringSkeletonsToSameAps autList

    let bringSkeletonPairToSameAps
        (skeleton1 : AlternatingAutomatonSkeleton<'T, 'L>)
        (skeleton2 : AlternatingAutomatonSkeleton<'T, 'L>)
        =
        AutomatonSkeleton.bringSkeletonPairToSameAps skeleton1 skeleton2

    let addAPsToSkeleton (aps : list<'L>) (skeleton : AlternatingAutomatonSkeleton<'T, 'L>) =
        AutomatonSkeleton.addAPsToSkeleton aps skeleton

    let fixAPsToSkeleton (aps : list<'L>) (skeleton : AlternatingAutomatonSkeleton<'T, 'L>) =
        AutomatonSkeleton.fixAPsToSkeleton aps skeleton

    let projectToTargetAPs (newAPs : list<'L>) (skeleton : AlternatingAutomatonSkeleton<'T, 'L>) =
        AutomatonSkeleton.projectToTargetAPs newAPs skeleton


    let computeBisimulationQuotient (accFunction : 'T -> 'G) (skeleton : AlternatingAutomatonSkeleton<'T, 'L>) =

        let explicitAlphabet =
            Util.computeBooleanPowerSet (skeleton.APs |> List.length) |> Seq.toList

        // Helper function to split a part of the partition
        let splitPartition (stateToPartitionId : Map<'T, int>) partitionId =
            let statesInPartitionId =
                stateToPartitionId
                |> Map.toSeq
                |> Seq.filter (fun (_, x) -> x = partitionId)
                |> Seq.map fst

            if Seq.length statesInPartitionId <= 1 then
                // This partition contains only one state, cannot be split further
                None
            else
                // We need to partiation states when, on some letter, the sets of sets of states are not the same

                let c =
                    statesInPartitionId
                    // Map all states to the successor partitions
                    |> Seq.map (fun s ->
                        // This id should be identical for all states in the same partition
                        let id =
                            explicitAlphabet
                            |> List.map (fun l ->
                                skeleton.Edges.[s]
                                |> List.filter (fun (g, _) -> g |> DNF.eval (fun i -> l.[i]))
                                |> List.map snd
                                |> List.map (fun y -> y |> Set.map (fun s' -> stateToPartitionId.[s']))
                                |> set
                            )

                        id, s
                    )
                    |> Seq.groupBy fst // group by the id
                    |> Seq.map (fun (k, el) -> k, el |> Seq.map snd |> set)
                    |> Map.ofSeq

                if Map.count c = 1 then
                    // All states point to the same set of partitions, no need to split
                    None
                else
                    Map.values c |> seq |> Some

        // We init the partition based only on the acceptance condition of each state
        let initStateToPartitionId =
            skeleton.States
            |> Seq.groupBy (fun s -> accFunction s)
            |> Seq.map snd
            |> Seq.mapi (fun i states -> states |> Seq.map (fun s -> s, i))
            |> Seq.concat
            |> Map.ofSeq

        let rec iterativeSplit (stateToPartitionId : Map<'T, int>) =
            let partitionIDs = stateToPartitionId |> Map.values |> Seq.distinct

            let mutable freshId = Seq.max partitionIDs + 1

            // Use lazyness here to not do all the work
            partitionIDs
            |> Seq.choose (fun id -> splitPartition stateToPartitionId id)
            |> Seq.tryHead
            |> function
                | None ->
                    // We are done, nothing left to split
                    stateToPartitionId
                | Some newPartitions ->

                    let newSplit =
                        // We do not assign the first partiation a new id as it can simply stay with the old one
                        (stateToPartitionId, Seq.tail newPartitions)
                        ||> Seq.fold (fun m states ->
                            let newId = freshId
                            freshId <- freshId + 1

                            (m, states)
                            ||> Set.fold (fun mm s ->
                                // Overwrite the partitionID for s
                                Map.add s newId mm
                            )
                        )

                    iterativeSplit newSplit

        let finalStateToPartitionId = iterativeSplit initStateToPartitionId

        let states = Map.values finalStateToPartitionId |> set

        let newSkeleton =
            {
                AutomatonSkeleton.States = states
                APs = skeleton.APs
                Edges =
                    states
                    |> Seq.map (fun id ->
                        // Any state in this partiition has the same set of set of states
                        let s =
                            finalStateToPartitionId
                            |> Map.toSeq
                            |> Seq.find (fun (_, idd) -> id = idd)
                            |> fst

                        let edges =
                            skeleton.Edges.[s]
                            |> List.map (fun (g, sucs) -> g, sucs |> Set.map (fun s' -> finalStateToPartitionId.[s']))

                        id, edges
                    )
                    |> Map.ofSeq
            }

        newSkeleton, finalStateToPartitionId



module NondeterministicAutomatonSkeleton =

    let actuallyUsedAPs (skeleton : NondeterministicAutomatonSkeleton<'T, 'L>) =
        AutomatonSkeleton.actuallyUsedAPs skeleton

    let mapAPs (f : 'L -> 'U) (skeleton : NondeterministicAutomatonSkeleton<'T, 'L>) =
        AutomatonSkeleton.mapAPs f skeleton

    let mapStates (f : 'T -> 'S) (skeleton : NondeterministicAutomatonSkeleton<'T, 'L>) =
        AutomatonSkeleton.mapStates f f skeleton

    let printBodyInHanoiFormat
        (stateStringer : 'T -> string)
        (accConditionStringer : 'T -> string)
        (skeleton : NondeterministicAutomatonSkeleton<'T, 'L>)
        =
        AutomatonSkeleton.printBodyInHanoiFormat stateStringer accConditionStringer stateStringer skeleton

    let findError (skeleton : NondeterministicAutomatonSkeleton<'T, 'L>) =
        try
            skeleton.States
            |> Seq.iter (fun x ->
                if skeleton.Edges.ContainsKey x |> not then
                    raise <| NotWellFormedException $"No edges defined for state $A{x}"

                skeleton.Edges.[x]
                |> List.iter (fun (g, t) ->
                    if skeleton.States.Contains t |> not then
                        raise
                        <| NotWellFormedException
                            $"State $A{t} is a conjunctive successor of states %A{x} but not defined as a state"

                    g
                    |> DNF.atoms
                    |> Set.iter (fun i ->
                        if i >= skeleton.APs.Length || i < 0 then
                            raise
                            <| NotWellFormedException
                                $"A transition guard from state $A{x} to %A{t} indexed to AP-index %i{i} which is out of range"
                    )
                )
            )

            None
        with NotWellFormedException msg ->
            Some msg

    let bringSkeletonsToSameAps (autList : list<NondeterministicAutomatonSkeleton<'T, 'L>>) =
        AutomatonSkeleton.bringSkeletonsToSameAps autList

    let bringSkeletonPairToSameAps
        (skeleton1 : NondeterministicAutomatonSkeleton<'T, 'L>)
        (skeleton2 : NondeterministicAutomatonSkeleton<'T, 'L>)
        =
        AutomatonSkeleton.bringSkeletonPairToSameAps skeleton1 skeleton2

    let addAPsToSkeleton (aps : list<'L>) (skeleton : NondeterministicAutomatonSkeleton<'T, 'L>) =
        AutomatonSkeleton.addAPsToSkeleton aps skeleton

    let fixAPsToSkeleton (aps : list<'L>) (skeleton : NondeterministicAutomatonSkeleton<'T, 'L>) =
        AutomatonSkeleton.fixAPsToSkeleton aps skeleton

    let projectToTargetAPs (newAPs : list<'L>) (skeleton : NondeterministicAutomatonSkeleton<'T, 'L>) =
        AutomatonSkeleton.projectToTargetAPs newAPs skeleton




    let toAlternatingAutomatonSkeleton (skeleton : NondeterministicAutomatonSkeleton<'T, 'L>) =
        {
            AutomatonSkeleton.States = skeleton.States
            APs = skeleton.APs
            Edges =
                skeleton.Edges
                |> Map.map (fun _ x -> x |> List.map (fun (g, t) -> g, Set.singleton t))
        }

    let tryFromAlternatingAutomatonSkeleton (skeleton : AlternatingAutomatonSkeleton<'T, 'L>) =
        let isNondeterminstic =
            skeleton.Edges
            |> Map.values
            |> List.concat
            |> List.map snd
            |> List.forall (fun x -> Set.count x = 1)

        if not isNondeterminstic then
            None
        else
            {
                AutomatonSkeleton.States = skeleton.States
                APs = skeleton.APs
                Edges =
                    skeleton.Edges
                    |> Map.map (fun _ x -> x |> List.map (fun (g, t) -> g, Seq.head t))
            }
            |> Some

    let computeBisimulationQuotient
        (accFunction : 'T -> 'G)
        (skeleton : NondeterministicAutomatonSkeleton<'T, 'L>)
        : NondeterministicAutomatonSkeleton<int, 'L> * Map<'T, int> =
        let bisim, m =
            skeleton
            |> toAlternatingAutomatonSkeleton
            |> AlternatingAutomatonSkeleton.computeBisimulationQuotient accFunction

        let skeleton = bisim |> tryFromAlternatingAutomatonSkeleton |> Option.get

        skeleton, m
