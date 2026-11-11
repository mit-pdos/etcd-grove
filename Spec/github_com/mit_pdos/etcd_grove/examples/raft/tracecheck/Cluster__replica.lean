/-
Lean-first (no Rocq counterpart). Trace-check's layer D, S7 (part 2) (2026-11-11).

`(*Cluster).replica(id)` (`examples/raft/tracecheck/concurrent.go`): the replica of id `id`, the
`id`-th of the cluster's slice (`replicas`, read-only once `RunConcurrent` has filled it), or `nil` for
`0` or an id past the slice (the network's `send` looks a message's destination up with it: a message
to an unknown id is dropped).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.RunConcurrent

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

/-- **The cluster's replicas, read-only**: its `replicas` field the slice of the replicas `rs`. -/
def replicasRO (c : Loc) (rs : List Loc) : IProp GF :=
  iprop(∃ sl : GoSlice, c.[G.Cluster, go!"replicas"] ↦□ sl ∗ sl ↦*□ rs)

instance replicasRO_persistent (c : Loc) (rs : List Loc) : Persistent (replicasRO (GF := GF) c rs) := by
  unfold replicasRO; infer_instance

/-- The replica of id `id` among `rs` (ids from `1`), `nil` if none. -/
def replicaOf (rs : List Loc) (id : w64) : Loc :=
  if uint.Z id = 0 ∨ (rs.length : Int) < uint.Z id then null else (rs[uint.nat id - 1]?).getD null

/-- See the file header. -/
abbrev Cluster.replica.spec : Prop :=
  ∀ (c : Loc) (rs : List Loc) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck ∗
      replicasRO c rs }}
    (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Cluster.ty @!! go!"replica")) (Val #id))
  {{ (r : Loc), RET #r; ⌜r = replicaOf rs id⌝ }}

end spec

end TraceCheck
end EtcdGrove
end Perennial
