/-
`Deployment.Node(n)`: the `n`-th client machine (`Deployment.nodeList`'s `n`-th entry): its workload's
index `j`, its index `c` in that workload, `ok` whether there is one. Soundness: `ok` only for an
entry of `nodeList`, and then `j`, `c` locate it in the workloads and the client machines' addresses.
Lean-first (no Rocq counterpart); N7-kv, M1 (`notes/etcd-dist-n7kv.md`).
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : deployment.Assumptions]

/-- Of a Go value `v` holding `d`: if `v.Node(n)` answers `ok`, `n` names `d.nodeList`'s entry of
workload `j`'s client machine `c`. -/
abbrev Deployment.Node.spec : Prop :=
  ∀ (v : deployment.Deployment) (d : Deployment) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment ∗
      deploymentRepr v d }}
    (App (Val #(methods deployment.Deployment.ty go!"Node" #v)) (Val #n))
  {{ (j c : w64) (ok : bool), RET (PairV (PairV #j #c) #ok);
      ⌜ok = true → 0 ≤ sint.Z n ∧ 0 ≤ sint.Z j ∧ 0 ≤ sint.Z c ∧
        ∃ w ns a, d.workloads[sint.nat j]? = some w ∧ d.nodes[sint.nat j]? = some ns ∧
          ns[sint.nat c]? = some a ∧ d.nodeList[sint.nat n]? = some (w, sint.nat c, a)⌝ }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
