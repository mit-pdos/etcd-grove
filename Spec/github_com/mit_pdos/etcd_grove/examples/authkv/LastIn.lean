/-
`LastIn(evs)` (`examples/authkv/authkv.go`; the auth plan's E2f). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Checks

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

/-- `LastIn(evs)` is the revision of the last event of `evs` in `[lo, hi)` (`lastIn`). -/
abbrev LastIn.spec : Prop :=
  ∀ (esl : GoSlice) (evs : List wev) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.authkv ∗
      esl ↦*{dq} evs }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.authkv.LastIn)) (Val #esl))
  {{ RET #(lastIn evs); esl ↦*{dq} evs }}

end spec

end authkv
end EtcdGrove
end Perennial
