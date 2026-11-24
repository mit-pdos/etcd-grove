/-
`deployment.AddrOk(a)`: the net extension's valid address (soundness: `true` only for one).
Lean-first (no Rocq counterpart); etcd_safe's deployment check (`notes/etcd-dist-plan.md`, D2).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : deployment.Assumptions]

/-- `AddrOk(a)` returns `true` only if `Net.addrOk a`. -/
abbrev deployment.AddrOk.spec : Prop :=
  ∀ (a : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment }}
    (App (Val (@! deployment.AddrOk)) (Val #a))
  {{ (b : Bool), RET #b; ⌜b = true → Net.addrOk a = true⌝ }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
