/- Lean-first (no Rocq counterpart).

# `etcd/dist/deployment`: a deployment's Go value in the heap

`deploymentRepr v d`: the Go struct value `v` of type `deployment.Deployment` holds the deployment `d`
(`TopLevelDefs.lean`'s mirror of the Go type): its slices (`Members`, `Workloads`, `Nodes` and each of
`Nodes`' inner slices) point, read-only (discarded fractions), to `d`'s lists, and its other fields are
`d`'s. Persistent: every program holding it (the boot programs, `WellFormed`, the workloads) shares
it. The composite literal `deploymentLit d` evaluates to such a value.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.TopLevelDefs
public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section vals
variable [GooseExts]

/-- A member's Go value. -/
def Member.val (m : Member) : deployment.Member := ⟨m.name, m.peer, m.client⟩

/-- A workload's Go value. -/
def Workload.val (w : Workload) : deployment.Workload := ⟨w.kind, w.clients, w.ops⟩

/-- The server configuration's Go value. -/
def ServerCfg.val (c : ServerCfg) : deployment.ServerCfg :=
  ⟨c.compactorMode, c.retention, c.snapCount, c.catchUp, c.auth⟩

end vals

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : deployment.Assumptions]

/-- **The Go value `v` holds the deployment `d`** (persistent): its slices point read-only to `d`'s
members, workloads and client machines' addresses (one inner slice per workload), and its token and
server configuration are `d`'s. -/
def deploymentRepr (v : deployment.Deployment) (d : Deployment) : IProp GF :=
  iprop(v.Members' ↦*□ d.members.map Member.val ∗
    ⌜v.Token' = d.token⌝ ∗ ⌜v.Cfg' = d.cfg.val⌝ ∗
    v.Workloads' ↦*□ d.workloads.map Workload.val ∗
    ∃ ss : List GoSlice, v.Nodes' ↦*□ ss ∗ [∗list] s;ns ∈ ss;d.nodes, s ↦*□ ns)

instance deploymentRepr_persistent (v : deployment.Deployment) (d : Deployment) :
    Persistent (deploymentRepr (GF := GF) v d) := by
  unfold deploymentRepr; infer_instance

open Iris.ProofMode in
/-- **Law**: the workloads' slice points read-only to `d`'s workloads (their Go values). -/
theorem deploymentRepr_workloads (v : deployment.Deployment) (d : Deployment) :
    deploymentRepr (GF := GF) v d ⊢ v.Workloads' ↦*□ d.workloads.map Workload.val := by
  iintro #Hd
  iunfold deploymentRepr at Hd
  icases Hd with ⟨-, -, -, #Hw, -⟩
  iexact Hw

open Iris.ProofMode in
/-- **Law**: the client machines' slice points read-only to one inner slice per workload, each
pointing read-only to that workload's client machines' addresses. -/
theorem deploymentRepr_nodes (v : deployment.Deployment) (d : Deployment) :
    deploymentRepr (GF := GF) v d ⊢
      iprop(∃ ss : List GoSlice, v.Nodes' ↦*□ ss ∗ [∗list] s;ns ∈ ss;d.nodes, s ↦*□ ns) := by
  iintro #Hd
  iunfold deploymentRepr at Hd
  icases Hd with ⟨-, -, -, -, %ss, #Hn, #Hns⟩
  iexists ss
  isplit
  · iexact Hn
  · iexact Hns

end defs

end etcd_dist
end EtcdGrove
end Perennial

end
