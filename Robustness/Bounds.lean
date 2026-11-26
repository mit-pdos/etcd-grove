/- Lean-first (no Rocq counterpart).

# Named bounds of the robustness statements

Constants a top-level statement's `threads` or `bound` (`Robustness.Robust`,
`Robustness/Statement.lean`) is set to when it is a real limit of Go rather than the no-cap
form (`threads := bound + 1`), named so that the statement says where the number comes from.
-/
module

@[expose] public section

namespace Perennial
namespace Robustness

/-- **Go's `rwmutexMaxReaders`** (`sync/rwmutex.go`: `const rwmutexMaxReaders = 1 << 30`):
a `sync.RWMutex` admits fewer than `2^30` readers at once (Perennial's model,
`sync.rwmutex.actualMaxReaders = 2^30 - 1`, lends its reader slots against live threads,
`Perennial/Proof/sync/RWMutexThreads.lean`). A statement about a program whose readers are its
threads bounds the live threads by it. -/
abbrev rwmutexMaxReaders : Nat := 2 ^ 30

end Robustness
end Perennial
