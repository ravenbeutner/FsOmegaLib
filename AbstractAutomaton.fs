module FsOmegaLib.AbstractAutomaton

open System
open AutomatonSkeleton

type AbstractAutomaton<'T, 'L when 'T: comparison and 'L : comparison> =
    abstract member ToHoaString : stateToString:('T -> String) -> apToString:('L -> String) -> String
    abstract member Skeleton : AutomatonSkeleton<'T, 'L>