/-
`syscall.Flock(fd, how)` (this repository's `syscall`, project `bboltfs`): trivial (D7 of
`notes/osfs-ext-plan.md`): with the fd open, any error. Proved in `Proof/syscall/Flock.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.syscall.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [syscall.Assumptions]

/-- See the file header. -/
abbrev syscall.Flock.spec : Prop :=
  ∀ (fd how : w64) (dq : DFrac) (d : OsFd),
  {{ osInv (GF := GF) ∗ osFd (GF := GF) fd dq d }}
    (App (App (Val (@! syscall.Flock)) (Val #fd)) (Val #how))
  {{ (e : w64), RET #(errnoErr e); osFd fd dq d }}

end spec

end EtcdGrove
end Perennial
