/- Lean-first (no Rocq counterpart).

`StartCluster(opts, dir)` (cluster.go): a cluster of the voters `1, …, opts.Voters` (`OptsOk`), their
files in the directory `dir`, holding none of them: from the files' entries at `none` (each voter's
file invariant allocated at the empty storage, with the id's durable state at `RaftState.init` and
its slot from the cluster's allocation, `cluster_alloc`), each voter started by `Cluster.start`
(`RestartNode` on an empty storage at the bootstrap configuration) under `c.mu`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- See the file header. -/
abbrev StartCluster.spec : Prop :=
  ∀ (γ : KdNames) (o : github_com.mit_pdos.etcd_grove.examples.kvdurable.Options) (dir : GoString),
  1 ≤ uint.Z o.Voters' → uint.Z o.Voters' ≤ 5 →
  let vs := kvreconf.bootVoters (uint.nat o.Voters')
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable ∗ context.isClosedchanInit ∗ kdCluster γ vs ∗
      kdStorInv ∗ ⌜γ.r.cluster.dup = true⌝ ∗
      ([∗list] id ∈ vs, raftState γ.r.cluster id RaftState.init ∗ nodeVacant γ.r.cluster id ∗
        dfile γ.files (kdFileName dir id) none ∗
        ∃ g : RaftState × Option GoString, ghostVar (γ.wr id) (1 : Qp) g) ∗
      joinAuth γ.r.cluster (GMap.listToSet vs) ∗
      ([∗list] i ∈ kvreconf.freshIds (vs.length + 1), dfile γ.files (kdFileName dir i) none ∗
        ∃ g : RaftState × Option GoString, ghostVar (γ.wr i) (1 : Qp) g) ∗
      ghostVar γ.r.opn (1 : Qp).half (W64 0) ∗ monoNatAuthOwn γ.r.nid 1 0 }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvdurable.StartCluster)) (Val #o)) (Val #dir))
  {{ (c : Loc), RET #c; isClusterC γ vs dir c }}

end spec

end kvdurable
end EtcdGrove
end Perennial
