
module FsOmegaLib.DPA

open System 
open System.IO

open SAT
open AutomatonSkeleton
open AbstractAutomaton

type DPA<'T, 'L when 'T: comparison and 'L : comparison> = 
    {
        Skeleton : AutomatonSkeleton<'T, 'L>
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
            this.Skeleton

        member this.ToHoaString (stateStringer : 'T -> String) (alphStringer : 'L -> String) =
            let s = new StringWriter() 

            s.WriteLine("HOA: v1")

            s.WriteLine ("States: " + string(this.States.Count))
            
            s.WriteLine ("Start: " + stateStringer(this.InitialState))

            s.WriteLine ("AP: " + string(this.APs.Length) + " " + List.fold (fun s x -> s + " \"" + alphStringer(x) + "\"") "" this.APs)

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

            s.WriteLine ("acc-name: parity max even " + string(maxColour + 1))
            s.WriteLine ("Acceptance: " + string(maxColour + 1) + " " + createParityString maxColour)

            s.WriteLine "--BODY--"
            
            for n in this.States do 
                let edges = this.Edges.[n]

                s.WriteLine("State: " + stateStringer(n) + " " + "{" + string(this.Color.[n]) + "}")

                for (g, n') in edges do 
                    s.WriteLine("[" + DNF.print g + "] " + stateStringer(n'))

            s.WriteLine "--END--"

            s.ToString()

module DPA = 
    let actuallyUsedAPs(dpa : DPA<'T, 'L>) = 
        AutomatonSkeleton.actuallyUsedAPs dpa.Skeleton

    let convertStatesToInt (dpa : DPA<'T, 'L>)  = 
        let idDict = 
            dpa.Skeleton.States
            |> Seq.mapi (fun i x -> x, i)
            |> Map.ofSeq

        {
            DPA.Skeleton = 
                {
                    AutomatonSkeleton.States = 
                        dpa.Skeleton.States
                        |> Set.map (fun x -> idDict.[x]);
                    APs = dpa.Skeleton.APs;
                    Edges = 
                        dpa.Skeleton.Edges 
                        |> Map.toSeq
                        |> Seq.map 
                            (fun (k, v) -> 
                                idDict.[k], v |> List.map (fun (g, s) -> g, idDict.[s])
                            )
                        |> Map.ofSeq;
                }

            InitialState = idDict.[dpa.InitialState];

            Color = 
                dpa.Color
                |> Map.toSeq
                |> Seq.map (fun (k, v) -> idDict.[k], v)
                |> Map.ofSeq;
        }
    
    let mapAPs (f : 'L -> 'U) (dpa : DPA<'T, 'L>) = 
        {
            Skeleton = AutomatonSkeleton.mapAPs f dpa.Skeleton
            InitialState = dpa.InitialState
            Color = dpa.Color
        }

    let trueAutomaton () : DPA<int, 'L> = 
        {
            DPA.Skeleton = {
                States = set([0])
                APs = []
                Edges = 
                    [0, [DNF.trueDNF, 0]]
                    |> Map.ofList
            }
            InitialState = 0
            Color = [0, 0] |> Map.ofList
        }

    let falseAutomaton () : DPA<int, 'L> = 
        {
            DPA.Skeleton = {
                States = set([0])
                APs = []
                Edges = 
                    [0, List.empty]
                    |> Map.ofList
            }
            InitialState = 0
            Color = [0, 1] |> Map.ofList
        }

    let toHoaString (stateStringer : 'T -> String) (alphStringer : 'L -> String) (dpa : DPA<'T, 'L>) = 
        (dpa :> AbstractAutomaton<'T, 'L>).ToHoaString stateStringer alphStringer

    let bringToSameAPs (autList : list<DPA<'T, 'L>>) =
        autList
        |> List.map (fun x -> x.Skeleton)
        |> AutomatonSkeleton.bringSkeletonsToSameAps 
        |> List.mapi (fun i x -> 
            {autList.[i] with Skeleton = x}
            )

    let bringPairToSameAPs (dpa1 : DPA<'T, 'L>) (dpa2 : DPA<'U, 'L>) =
        let sk1, sk2 = AutomatonSkeleton.bringSkeletonPairToSameAps dpa1.Skeleton dpa2.Skeleton

        {dpa1 with Skeleton = sk1}, {dpa2 with Skeleton = sk2}

    let addAPs (aps : list<'L>)  (dpa : DPA<'T, 'L>) =
        {dpa with Skeleton = AutomatonSkeleton.addAPsToSkeleton aps dpa.Skeleton}

    let fixAPs (aps : list<'L>)  (dpa : DPA<'T, 'L>) =
        {dpa with Skeleton = AutomatonSkeleton.fixAPsToSkeleton aps dpa.Skeleton}

    let projectToTargetAPs (newAPs : list<'L>) (dpa : DPA<int, 'L>)  = 
        {dpa with Skeleton = AutomatonSkeleton.projectToTargetAPs newAPs dpa.Skeleton}
