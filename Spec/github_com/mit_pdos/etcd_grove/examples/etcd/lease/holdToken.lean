/-
`holdToken()` (`examples/etcd/lease/etcd_lease.go`; the closed lease example, `notes/lease-ex-plan.md`,
"The run's thread token"): sleeps forever. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.lease.Main

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_lease

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.lease.Assumptions]

/-- `holdToken()` does not return (`False` after it): the goroutine `Main` runs it on holds no
resource and never ends, so `Main` keeps the token `wp_fork_tok_self` gives it. -/
abbrev holdToken.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.lease }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.lease.holdToken)) (Val #()))
  {{ RET #(); False }}

end spec

end etcd_lease
end EtcdGrove
end Perennial
