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

module internal FsOmegaLib.Util

open System

let rec cartesianProduct (LL : list<seq<'a>>) =
    match LL with
    | [] -> Seq.singleton []
    | L :: Ls ->
        seq {
            for x in L do
                for xs in cartesianProduct Ls -> x :: xs
        }

let rec computeBooleanPowerSet n =
    if n = 0 then
        Seq.singleton []
    else
        let r = computeBooleanPowerSet (n - 1)
        Seq.append (Seq.map (fun x -> true :: x) r) (Seq.map (fun x -> false :: x) r)

module SubprocessUtil =

    type SubprocessResult =
        {
            Stdout : string
            Stderr : string
            ExitCode : int
        }

    let executeSubprocess (envVariables : Map<string, string>) (cmd : string) (arg : string) =
        let psi = System.Diagnostics.ProcessStartInfo(cmd, arg)

        psi.UseShellExecute <- false
        psi.RedirectStandardOutput <- true
        psi.RedirectStandardError <- true
        psi.CreateNoWindow <- true

        for (var, v) in Map.toSeq envVariables do 
            psi.Environment.Add(var, v)

        let p = System.Diagnostics.Process.Start(psi)
        let output = System.Text.StringBuilder()
        let error = System.Text.StringBuilder()

        p.OutputDataReceived.Add(fun args -> output.Append(args.Data + "\n") |> ignore)
        p.ErrorDataReceived.Add(fun args -> error.Append(args.Data + "\n") |> ignore)
        p.BeginErrorReadLine()
        p.BeginOutputReadLine()
        p.WaitForExit()

        {
            SubprocessResult.Stdout = output.ToString().Trim()
            Stderr = error.ToString().Trim()
            ExitCode = p.ExitCode
        }
