module FsOmegaLib.AutomatonSkeleton

open System 
open SAT 

type AutomatonSkeleton<'T, 'L when 'T: comparison and 'L : comparison> = 
    {
        States : Set<'T>
        APs: list<'L>
        Edges: Map<'T, list<DNF<int> * 'T>>
    }

module AutomatonSkeleton = 

    let actuallyUsedAPs(skeleton : AutomatonSkeleton<'T, 'L>) = 
        skeleton.Edges
        |> Seq.map (fun x -> 
            x.Value
            |> List.map ((fun (g, _) -> DNF.atoms g))
            |> Set.unionMany
        )
        |> Set.unionMany 
        |> Set.map (fun i -> skeleton.APs.[i])


    let mapAPs (f : 'L -> 'U) (skeleton : AutomatonSkeleton<'T, 'L>) = 
        {
            States = skeleton.States;
            APs = skeleton.APs |> List.map f
            Edges = skeleton.Edges
        }
 
    let bringSkeletonsToSameAps (autList : list<AutomatonSkeleton<'T, 'L>>) =
        let combinedAps = 
            autList
            |> List.map (fun x -> x.APs)
            |> List.concat
            |> List.distinct

        let remapSkeleton (skeleton: AutomatonSkeleton<'X,'L>) = 
            let apAlignment i =
                List.findIndex ((=) skeleton.APs.[i]) combinedAps
            {
                skeleton with 
                    APs = combinedAps; 
                    Edges = 
                        skeleton.Edges
                        |> Map.map (fun _ e -> 
                            e |> List.map (fun (g, s) -> DNF.map apAlignment g, s) 
                            )
            }

        autList
        |> List.map remapSkeleton

    let bringSkeletonPairToSameAps (skeleton1 : AutomatonSkeleton<'T, 'L>) (skeleton2 : AutomatonSkeleton<'U, 'L>) =
        let combinedAps = 
            List.append skeleton1.APs skeleton2.APs
            |> List.distinct

        let remapSkeleton (skeleton: AutomatonSkeleton<'X,'L>) = 
            let apAlignment i =
                List.findIndex ((=) skeleton.APs.[i]) combinedAps
            {
                skeleton with 
                    APs = combinedAps; 
                    Edges = 
                        skeleton.Edges
                        |> Map.map (fun _ e -> 
                            e |> List.map (fun (g, s) -> DNF.map apAlignment g, s) 
                            )
            }

        remapSkeleton skeleton1, remapSkeleton skeleton2

    let addAPsToSkeleton (aps : list<'L>)  (skeleton : AutomatonSkeleton<'T, 'L>) =
        let combinedAps = 
            List.append skeleton.APs aps
            |> List.distinct

        let remapSkeleton (skeleton: AutomatonSkeleton<'X,'L>) = 
            let apAlignment i =
                List.findIndex ((=) skeleton.APs.[i]) combinedAps
            {
                skeleton with 
                    APs = combinedAps; 
                    Edges = 
                        skeleton.Edges
                        |> Map.map (fun _ e -> 
                            e |> List.map (fun (g, s) -> DNF.map apAlignment g, s) 
                            )
            }

        remapSkeleton skeleton

    let fixAPsToSkeleton (aps : list<'L>)  (skeleton : AutomatonSkeleton<'T, 'L>) =
        skeleton.APs
        |> List.iter (fun x -> 
            if List.contains x aps |> not then 
                raise <| Exception($"%A{x} was not contained in the APs to be fixed")
            ()
            )
        
        let remapSkeleton (skeleton: AutomatonSkeleton<'X,'L>) = 
            let apAlignment i =
                List.findIndex ((=) skeleton.APs.[i]) aps
            {
                skeleton with 
                    APs = aps; 
                    Edges = 
                        skeleton.Edges
                        |> Map.map (fun _ e -> 
                            e |> List.map (fun (g, s) -> DNF.map apAlignment g, s) 
                            )
            }

        remapSkeleton skeleton

    let projectToTargetAPs (newAPs : list<'L>) (skeleton : AutomatonSkeleton<int, 'L>)  = 

        let apRemapping = 
            newAPs
            |> List.mapi (fun i x ->  List.findIndex ((=) x) skeleton.APs, i)
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

