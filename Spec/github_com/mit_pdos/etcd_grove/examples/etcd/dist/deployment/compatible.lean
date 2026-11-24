/-
`deployment.compatible(ws)`: the workloads can run at once (soundness: `true` only if so).
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

/-- `compatible(ws)`, of a read-only slice of the workloads `ws`, returns `true` only if
`goCompatible ws`. -/
abbrev compatible.spec : Prop :=
  ∀ (sl : GoSlice) (ws : List Workload),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment ∗ sl ↦*□ ws.map Workload.val }}
    (App (Val (@! deployment.compatible)) (Val #sl))
  {{ (b : Bool), RET #b; ⌜b = true → goCompatible ws⌝ }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
