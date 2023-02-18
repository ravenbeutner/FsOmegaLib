# FsOmegaLib

An F# library for omega-Automata and LTL formulas.
The library provides datatypes to represent NBAs, GNBAs, DPAs, and LTL formulas and functions for automata conversions and operations (complementation, union, intersection, etc.).
Automata transformations and operations are handled by system calls to [spot](https://spot.lre.epita.fr/).
The relevant methods require a path to the spot executables (such as spot's *autfilt* and *ltl2tgba*).