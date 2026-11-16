/- Lean-first (no Rocq counterpart).

`RandomOptionsN(k)` (cluster.go; 2026-11-16, kvraftN): `RandomOptions()`'s random options on `k`
voters, with up to `k + 4` replicas: for `1 ≤ k < 2^59` (`k + 4` below `2^60`), options a cluster
may run with (`kdOptsOk`) of `k` voters and `k + 4` replicas.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvdurable.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvdurable.Assumptions]

/-- See the file header. -/
abbrev RandomOptionsN.spec : Prop :=
  ∀ (k : w64), 1 ≤ uint.Z k → uint.Z k < 2 ^ 59 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvdurable }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvdurable.RandomOptionsN)) (Val #k))
  {{ (o : KOptions), RET #o; ⌜kdOptsOk o ∧ o.Voters' = k ∧ o.MaxReplicas' = k + W64 4⌝ }}

end spec

end raft_kvdurable
end EtcdGrove
end Perennial
