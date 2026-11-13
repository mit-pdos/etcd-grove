/-
The proof of `Spec/os/File__TruncateAu.lean` (I3b): **`sorry`**. Plan: `File__Truncate.lean`'s Löb
loop, its state `ftState` at half (the caller's halves of an attempt's start state, `os.TruncFrom`),
each attempt `wp_osFtruncateStart_au` with the supply's `os.truncAu` for that state, then
`wp_osFtruncateFinish_au` with the commit's update; the outcome's halves (`os.truncOutH`) re-enter the
loop on `EINTR` (`os.announce_idem`, `os.rsPost_announce`, `os.rsPost_rsPost` relate the states to
`m`'s). Lean-first.
-/
module

public import LinuxFs.Spec.os.File__TruncateAu

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

theorem os.File.Truncate.wp_proofAu : os.File.Truncate.specAu (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
