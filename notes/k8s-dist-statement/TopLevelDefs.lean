/- DRAFT (K1, 2026-11-28; not built: `notes/` is in no `lean_lib`). Proposed
`Proof/github_com/mit_pdos/etcd_grove/examples/k8s/dist/TopLevelDefs.lean`, the defs module the
statement names (`notes/k8s-dist-statement-packet.md` §1). Mirrors etcd-dist's `TopLevelDefs.lean`
(`Proof/.../examples/etcd/dist/TopLevelDefs.lean:60-260`); only what differs is written out. -/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.TopLevelDefs
public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.k8s.dist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_dist

/-! ## The deployment (Go's `dist.Deployment`, `examples/k8s/dist/deploy.go`) -/

/-- Go's `dist.Workload` (`dist.go`): its kind (`Store` 0, `Compactor` 1) and sizes, every field a Go
`int`. -/
structure Workload where
  kind : w64
  clients : w64
  ops : w64
  watchers : w64
  wops : w64
  apiservers : w64
  rounds : w64

/-- Go's `dist.Deployment`: the etcd cluster (an etcd-dist deployment; `WellFormed` requires no etcd
workload, no auth, no etcd compactor), the store and compactor workloads over it, and their client
machines' addresses. -/
structure Deployment where
  cluster : etcd_dist.Deployment
  storeW : Workload
  compW : Workload
  storeAddrs : List GoString
  compAddrs : List GoString

/-- How many client machines `d` has (Go's `NodeCount(d.StoreW) + NodeCount(d.CompW)`; on a deployment
`WellFormed` refuses, the machines past the ones `Deployment.Node` names return at once). The
compactor's count is the translation's constant `CompactorMachines` (writer, own compactors, shared one),
named, not a literal. -/
def Deployment.nodeCount (d : Deployment) : Nat :=
  sorry -- K3: `nodeCountGo d.storeW + nodeCountGo d.compW`, `NodeCount`'s Lean image

section programs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

open github_com.mit_pdos.etcd_grove.examples.k8s

/-- The deployment as a Go value: `dist.Deployment{Cluster: <etcd_dist.deploymentLit d.cluster>,
StoreW: …, CompW: …, StoreAddrs: …, CompAddrs: …}`, field for field `d` (as `etcd_dist.deploymentLit`). -/
def deploymentLit (d : Deployment) : Expr := sorry -- K3, the same construction as etcd-dist's

/-- **Member `i`'s machine**: etcd-dist's member program on the cluster, unchanged
(`server.MainDeployment(d.Cluster, i)`, at the first start and, in the crash version, after every
crash). -/
def serverProg (d : Deployment) (i : Nat) : Expr := etcd_dist.serverProg d.cluster i

/-- **Workload `j`'s orchestrator machine** (`0` the store, `1` the compactor): `dist`'s
initialization, then `dist.Orchestrator(d, j)` (`WellFormed(d)`, then `MainReady`). -/
def orchProg (d : Deployment) (j : Nat) : Expr :=
  dist.initialize' #() ;;
  App (App (Val (@! dist.Orchestrator)) (deploymentLit d)) (Val #(W64 j))

/-- **The `n`-th client machine** (the store's API server machines, then the compactor's writer and
API server machines): `dist`'s initialization, then `dist.NodeDeployment(d, n)` (`WellFormed(d)`, then
`NodeMain`). -/
def nodeProg (d : Deployment) (n : Nat) : Expr :=
  dist.initialize' #() ;;
  App (App (Val (@! dist.NodeDeployment)) (deploymentLit d)) (Val #(W64 n))

/-- **Every machine**: the members', the two orchestrators', the client machines'. -/
def machines (d : Deployment) (σs σo σn : List state) : List (Expr × state) :=
  σs.mapIdx (fun i σ => (serverProg d i, σ)) ++
  σo.mapIdx (fun j σ => (orchProg d j, σ)) ++
  σn.mapIdx (fun n σ => (nodeProg d n, σ))

/-- The number of orchestrator machines: one per workload (Go's `StoreWorkload`, `CompactorWorkload`). -/
def orchCount : Nat := 2

end programs

end k8s_dist
end EtcdGrove
end Perennial
