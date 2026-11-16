/- Lean-first (no Rocq counterpart).

`RandomOptionsN(k)` (cluster.go; 2026-11-16, kvraftN): `RandomOptions()`'s random options on `k`
voters, with up to `k + 4` replicas: for `1 ≤ k < 2^59` (`k + 4` below `2^60`), options a cluster
may run with (`OptsOk`) of `k` voters.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.DefsCluster

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvreconf

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Assumptions]

/-- See the file header. -/
abbrev RandomOptionsN.spec : Prop :=
  ∀ (k : w64), 1 ≤ uint.Z k → uint.Z k < 2 ^ 59 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.RandomOptionsN)) (Val #k))
  {{ (o : ROptions), RET #o; ⌜OptsOk o ∧ o.Voters' = k⌝ }}

end spec

end raft_kvreconf
end EtcdGrove
end Perennial
