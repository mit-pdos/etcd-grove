/- Lean-first (no Rocq counterpart).

`r.snapshot(req, known)` (kv.go): what the request asks (`snapReqOk`): `CreateSnapshot` under `dmu`
(tolerating `ErrSnapOutOfDate`), a compaction under `dmu` to a random index from the first one to the
least of the requested bound and `known`; then, if either changed the storage, one time in two
`persist` (with the snapshotter's share of `nodeRunning`). It returns a lower bound of the stored
snapshot's index.
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
abbrev Replica.snapshot.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (r n st sts sq : Loc)
    (ρ : KdRepNames) (q : KSnapReq) (known : w64) (qp : Qp),
  {{ isReplicaR γ vs dir id r n st sts sq ρ ∗ snapReqOk γ ρ.key ρ.γs q ∗
      memSnapLb ρ.γs (uint.nat known) ∗ nodeRunning n γ.r.cluster kdRaftN qp }}
    (App (App (Val (r @!! go.GoType.PointerType kReplicaTy @!! go!"snapshot")) (Val #q)) (Val #known))
  {{ (known' : w64), RET #known'; memSnapLb ρ.γs (uint.nat known') ∗
      nodeRunning n γ.r.cluster kdRaftN qp }}

end spec

end kvdurable
end EtcdGrove
end Perennial
