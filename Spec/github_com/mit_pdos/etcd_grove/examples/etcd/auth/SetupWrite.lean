/-
`SetupWrite(e)` (`examples/etcd/auth/etcd_auth.go`; F-S1 of `notes/authkv-main-plan.md`, round 3).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.Checks

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.auth.Assumptions]

/-- `SetupWrite(e)` is whether `e` is one of the set-up's puts (`setupWriteK`: a put of a key of
`setupKeys` with the value `setup`). -/
abbrev SetupWrite.spec : Prop :=
  ∀ (e : wev),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.auth }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.auth.SetupWrite)) (Val #e))
  {{ RET #(decide (setupWriteK e.Put' e.Key' e.Val')); True }}

end spec

end etcd_auth
end EtcdGrove
end Perennial
