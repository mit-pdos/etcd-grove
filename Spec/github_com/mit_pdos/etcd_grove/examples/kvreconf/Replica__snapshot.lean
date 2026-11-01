/- Lean-first (no Rocq counterpart).
`r.snapshot(q, known)` (kv.go; kvreconf-snapshot-thread, 2026-10-30): the snapshot goroutine does
what the request `q` asks (`snapReqOk`): `CreateSnapshot`, whose `ErrSnapOutOfDate` it tolerates
(the stored snapshot is at least as recent: `run` installed one), and a compaction to some index
from the first one to the least of `q.compact` and `known`, the index the stored snapshot is known
to have reached (`memSnapLb`). It returns what is known after it. No panic: `CreateSnapshot`
answers `nil` or `ErrSnapOutOfDate`.
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
abbrev Replica.snapshot.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (id : w64) (r n st sts : Loc) (ρ : RepNames) (q : RSnapReq)
    (known : w64),
  {{ isReplicaR γr vs id r n st sts ρ ∗ snapReqOk γr id ρ.γs q ∗ memSnapLb ρ.γs (uint.nat known) }}
    (App (App (Val (r @!! go.GoType.PointerType rReplicaTy @!! go!"snapshot")) (Val #q)) (Val #known))
  {{ (known' : w64), RET #known'; memSnapLb ρ.γs (uint.nat known') }}

end spec

end kvreconf
end EtcdGrove
end Perennial
