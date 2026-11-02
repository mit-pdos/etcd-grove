/- Lean-first (no Rocq counterpart).

`r.persist()` (kv.go): under `dmu`, unless the incarnation crashed, the storage's contents `M`
written to the file (`durable.Write(file, string(encode()))`, logically atomic: the file's invariant
opened in its update), firing the pending batch's *enter* there (`readyEnter`, with the caller's share
`q` of `nodeRunning`): the durable state moves to the batch's, which `M` holds, the file to `M`; a
batch fired by another writer's `persist` is left in `dmu` for `run` (`KdPhase.fired`). It returns
whether it wrote (false: crashed, nothing written). For `run`'s own batch (`stI`, `stI'`, `ms` the
`Ready`'s): when it wrote, the batch is entered, and `run` gets its driver and messages.
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

/-- See the file header. The caller holds no claim on the pending batch (the snapshotter's
`persist`): a batch pending in `dmu` is entered by this write and left `fired` for `run`. -/
abbrev Replica.persist.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (r n st sts sq ms : Loc)
    (γs : MemStorNames) (ph : KdDmuNames) (q : Qp),
  {{ isReplica γ vs dir id r n st sts sq ms γs ph ∗ nodeRunning n γ.r.cluster kdRaftN q }}
    (App (Val (r @!! go.GoType.PointerType kReplicaTy @!! go!"persist")) (Val #()))
  {{ (ok : Bool), RET #ok; nodeRunning n γ.r.cluster kdRaftN q }}

/-- `persist` called by `run` with its batch pending (`KdPhase.waiting … γb` in `dmu`, which `run`'s
`dmu` section put there): when it writes, the batch is entered (by this write or an earlier one of
the snapshotter's, `KdPhase.fired`), and `run` gets the loop's token at `st'` and the messages sent
(`kdBatchRes`). (The other callers, the snapshotter's, hold no claim: `persist.spec`.) -/
abbrev Replica.persist.specRun : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (r n st sts sq ms : Loc)
    (γs : MemStorNames) (ph : KdDmuNames) (q : Qp) (st' : NodeDriverState) (qs : List QMsg) (γb : GName),
  {{ isReplica γ vs dir id r n st sts sq ms γs ph ∗ nodeRunning n γ.r.cluster kdRaftN q ∗
      -- `run`'s claim on its batch (the pending phase's variable, `dmu`'s other half), whose
      -- results are saved at `γb`
      -- (2026-11-01, stage II (h)) with the batch's durable state, `dmu`'s once it is entered
      ghostVar ph.ph (1 : Qp).half (some γb, st'.durable) ∗
      savedPropOwn γb DFrac.discard (kdBatchRes γ id n st' qs) }}
    (App (Val (r @!! go.GoType.PointerType kReplicaTy @!! go!"persist")) (Val #()))
  {{ (ok : Bool), RET #ok; nodeRunning n γ.r.cluster kdRaftN q ∗
      (if ok then iprop(ghostVar ph.ph (1 : Qp).half ((none : Option GName), st'.durable) ∗
         kdBatchRes γ id n st' qs)
       else iprop(ghostVar ph.ph (1 : Qp).half (some γb, st'.durable))) }}

end spec

end kvdurable
end EtcdGrove
end Perennial
