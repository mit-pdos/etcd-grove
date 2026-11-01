/- Lean-first (no Rocq counterpart).

`StartCluster(opts)` (cluster.go): a cluster of `opts.Voters` voters, ids `1 … Voters`, each a
`RestartNode` on a fresh registered storage answering the bootstrap conf state. Everything else is
allocated in the proof: raft's cluster (`cluster_alloc`, `dup = true`), the store's decisions
(`confPolicy`), snapshot registry and invariant; the client gets the store's state (`rkvVal`, the
empty store) and the stopper's token. Needs the storage registry (`kvrStorInv`) and raft's step
bound (`receiptBound GF ≤ 2^64 - 2`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.DefsCluster

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

/-- See the file header. -/
abbrev StartCluster.spec : Prop :=
  ∀ (o : ROptions),
  OptsOk o → receiptBound GF ≤ 2 ^ 64 - 2 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvreconf ∗ context.isClosedchanInit ∗ kvrStorInv }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvreconf.StartCluster)) (Val #o))
  {{ (c : Loc), RET #c; ∃ γr : RNames,
      isClusterC γr (bootVoters (uint.nat o.Voters')) c ∗ rkvVal γr kvEmpty ∗ stopper γr }}

end spec

end kvreconf
end EtcdGrove
end Perennial
