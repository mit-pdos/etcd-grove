/-
`LastIn(evs)` (`examples/lib/authwork/etcd_auth.go`; the auth plan's E2f). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.authwork.Checks

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_auth

open Iris Iris.BI etcdstart

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.authwork.Assumptions]

/-- `LastIn(evs)` is the revision of the last event of `evs` in `[lo, hi)` (`lastIn`). -/
abbrev LastIn.spec : Prop :=
  ∀ (esl : GoSlice) (evs : List wev) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.authwork ∗
      esl ↦*{dq} evs }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.authwork.LastIn)) (Val #esl))
  {{ RET #(lastIn evs); esl ↦*{dq} evs }}

end spec

end etcd_auth
end EtcdGrove
end Perennial
