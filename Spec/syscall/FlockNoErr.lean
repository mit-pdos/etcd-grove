/-
`syscall.Flock(fd, how)` with no error of the environment (`Flock.spec` over a semantics whose steps
satisfy **no error of `flock`, `mmap`, `munmap` on chosen files**, `FsStepSat (NoMapLockErr Sio)`,
pending the user's review; every inode covered), of an unlock or a non-blocking request: errno 0, or
`EAGAIN` for a lock request (another description's conflicting lock). Proved in
`Proof/syscall/FlockNoErr.lean`. Lean-first.
-/
module

public import Spec.syscall.Flock
public import GooseLang.Ext.Fs.Premises
public import GooseLang.Ext.Fs.FilteredSem

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [syscall.Assumptions]

/-- See the file header. -/
abbrev syscall.Flock.specNoErr : Prop :=
  ∀ (Sio : IoSet) [FsStepSat (NoMapLockErr Sio)], (∀ st i, Sio.ino st i) →
  ∀ (fd how : w64) (d : OsFd) (req : Option Bool) (nb : Bool),
  flockReq how.toNat = some (req, nb) → (req ≠ none → d.flk = none) → (req = none ∨ nb = true) →
  {{ osInv (GF := GF) ∗ osFd (GF := GF) fd (DFrac.own 1) d ∗ lockTok (GF := GF) .flock fd d }}
    (App (App (Val (@! syscall.Flock)) (Val #fd)) (Val #how))
  {{ (e : w64), RET #(errnoErr e); ⌜e = 0 ∨ (req ≠ none ∧ e = EAGAIN)⌝ ∗
      lockOut (GF := GF) .flock fd d req e }}

end spec

end EtcdGrove
end Perennial
