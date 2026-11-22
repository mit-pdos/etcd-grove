/- Lean-first (no Rocq counterpart).

`r.persist()` (`examples/raft/kvnet/replica.go`): under `dmu`, the storage's contents `M` written to the
replica's file (`durable.Write(file, string(storage.encode()))`, over fsExt: decision C,
`notes/kvnet-part.md`, "`persist`"), in `durable`'s two atomic updates. At the rename the file's
invariant (`kdFileInvK`) enters the write's window, keeping the pending batch's *enter* (`readyEnter`)
there. At the directory's sync (with the crash token) the *enter* fires with the caller's share `q` of
`nodeRunning`: the durable state moves to the batch's, which `M` holds. A batch pending in `dmu`
(`KdPhase.waiting`) is entered by whichever writer writes first and left `fired` for `run`. For
`run`'s own batch (`specRun`): the batch is entered, and `run` gets its driver and messages.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

/-- See the file header. The caller holds no claim on the pending batch (the snapshotter's
`persist`): a batch pending in `dmu` is entered by this write and left `fired` for `run`. -/
abbrev Replica.persist.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (r : Loc) (n : NodeH) (st sts sq ms : Loc)
    (γs : MemStorNames) (ph : KdDmuNames) (q : Qp),
  {{ isReplica γ vs dir id r n st sts sq ms γs ph ∗ nodeRunning (GF := GF) n γ.r.cluster kdRaftN q }}
    (App (Val (r @!! go.GoType.PointerType kReplicaTy @!! go!"persist")) (Val #()))
  {{ RET #(); nodeRunning n γ.r.cluster kdRaftN q }}

/-- `persist` called by `run` with its batch pending (`KdPhase.waiting … γb` in `dmu`, which `run`'s
`dmu` section put there): the batch is entered (by this write or an earlier one of the snapshotter's,
`KdPhase.fired`), and `run` gets the loop's token at `st'` and the messages sent (`kdBatchRes`). (The
snapshotter holds no claim: `persist.spec`.) -/
abbrev Replica.persist.specRun : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (r : Loc) (n : NodeH) (st sts sq ms : Loc)
    (γs : MemStorNames) (ph : KdDmuNames) (q : Qp) (st' : NodeDriverState) (qs : List QMsg) (γb : GName),
  {{ isReplica γ vs dir id r n st sts sq ms γs ph ∗ nodeRunning n γ.r.cluster kdRaftN q ∗
      ghostVar ph.ph (1 : Qp).half (some γb, st'.durable) ∗
      savedPropOwn γb DFrac.discard (kdBatchRes γ id n st' qs) }}
    (App (Val (r @!! go.GoType.PointerType kReplicaTy @!! go!"persist")) (Val #()))
  {{ RET #(); nodeRunning n γ.r.cluster kdRaftN q ∗
      ghostVar ph.ph (1 : Qp).half ((none : Option GName), st'.durable) ∗ kdBatchRes γ id n st' qs }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
