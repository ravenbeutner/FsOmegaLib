module internal FsOmegaLib.Util
#nowarn "59"

open System
open System.Collections.Generic

let rec combineStringsWithSeperator (s: String) (l: list<String>) = 
    match l with 
    | [] -> ""
    | [x] -> x
    | x::y::xs -> 
        x + s + combineStringsWithSeperator s (y::xs)

let rec cartesianProduct (LL: list<seq<'a>>) =
    match LL with
    | [] -> Seq.singleton []
    | L :: Ls ->
        seq {
            for x in L do
                for xs in cartesianProduct Ls -> x :: xs
        }

let dictToMap (d : Dictionary<'A, 'B>) = 
    d 
    |> Seq.map (fun x -> x.Key, x.Value)
    |> Map.ofSeq

module SystemCallUtil = 

    type SystemCallResult = 
        | SystemCallSuccess of String
        | SystemCallError of String
        | SystemCallTimeout

    let systemCall cmd arg timeout =
        let p = new System.Diagnostics.Process();
        p.StartInfo.RedirectStandardOutput <- true
        p.StartInfo.RedirectStandardError <- true
        p.StartInfo.UseShellExecute <- false
        p.StartInfo.FileName <- cmd
        p.StartInfo.Arguments <- arg
        p.Start() |> ignore 

        let a = 
            match timeout with 
                | Option.None -> 
                    true
                | Some t -> 
                    
                    p.WaitForExit(t :> int)

        if a then 
            let err = p.StandardError.ReadToEnd() 

            if err <> "" then 
                SystemCallError err
            else 
                let res = p.StandardOutput.ReadToEnd()
                p.Kill true
                SystemCallSuccess res
        else 
            p.Kill true
            SystemCallTimeout
            
