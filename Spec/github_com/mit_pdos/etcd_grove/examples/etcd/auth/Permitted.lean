/-
`Permitted(who, k)` (`examples/etcd/auth/etcd_auth.go`; the auth plan's E2b). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.auth.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_auth

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.auth.Assumptions]

/-- `Permitted(who, k)` is `who = u ∧ k ∈ [lo, hi)` (`permittedK`), the model's verdict at the
set-up's state for the workload's principals (`granted_setupSt_iff`). -/
abbrev Permitted.spec : Prop :=
  ∀ (who k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.auth }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.auth.Permitted)) (Val #who))
      (Val #k))
  {{ RET #(decide (permittedK who k)); True }}

end spec

end etcd_auth
end EtcdGrove
end Perennial
