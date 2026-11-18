/-
`syscall.Flock(fd, how)`, non-blocking or `LOCK_UN`, whose errno other than a lock request's `EAGAIN`
witnesses that **the file system can fail** (`Flock.spec` with `⌜e = 0 ∨ (req ≠ none ∧ e = EAGAIN) ∨
¬ FsNoErr⌝`; session S3f of `notes/bbolt-integration-plan.md`): under the premises `FsNoErr` names,
`specNoErr`. Proved in `Proof/syscall/FlockW.lean`, from the two.
-/
module

public import Spec.syscall.Flock
public import GooseLang.Ext.Fs.FsNoErr

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
abbrev syscall.Flock.specW : Prop :=
  ∀ (fd how : w64) (d : OsFd) (req : Option Bool) (nb : Bool),
  flockReq how.toNat = some (req, nb) → (req ≠ none → d.flk = none) → (req = none ∨ nb = true) →
  {{ osInv (GF := GF) ∗ osFd (GF := GF) fd (DFrac.own 1) d ∗ lockTok (GF := GF) .flock fd d }}
    (App (App (Val (@! syscall.Flock)) (Val #fd)) (Val #how))
  {{ (e : w64), RET #(errnoErr e); ⌜e = 0 ∨ (req ≠ none ∧ e = EAGAIN) ∨ ¬ FsNoErr⌝ ∗
      lockOut (GF := GF) .flock fd d req e }}

end spec

end EtcdGrove
end Perennial
