/-
`holdToken()` (`examples/lib/cluster3/cluster3.go`; lease-mono3's pass 2(a), 2026-11-06,
`notes/lease-mono3-plan.md`, finding 1 (i); leasegrant's `holdToken`, `notes/lease-ex-plan.md`, "The
run's thread token"): sleeps forever. Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cluster3

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Assumptions]

/-- `holdToken()` does not return (`False` after it): the goroutine `StartMember` runs it on holds
no resource and never ends, so `StartMember` keeps the token `wp_fork_tok_self` gives it. -/
abbrev holdToken.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.cluster3 }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.cluster3.holdToken)) (Val #()))
  {{ RET #(); False }}

end spec

end cluster3
end EtcdGrove
end Perennial
