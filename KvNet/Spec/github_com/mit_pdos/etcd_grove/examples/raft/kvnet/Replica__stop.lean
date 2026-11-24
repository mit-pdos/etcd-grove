/- Lean-first (no Rocq counterpart). kvdurable's `Replica.stop` with its `crash`'s last `dmu` section
(2026-11-24, G5 of the raft subsumption: the clean stop and restart in the process).

`r.stop()` (replica.go): closes `stopc`; receives on `runDone` (`run`'s half of `nodeRunning` and its
claim on the pending batch, `ρ.ph.ph`, at `none`: no batch waits, so the file is outside a write's
window), `tickDone` and `snapDone` (the snapshotter's half); stops the node (raft's `node.Stop`:
`nodeVacantA γ id x` with `nodeArm n γ x`, so `x` is the generation's arm, `nodeArm_agree`); then takes
`dmu` and never releases it (nothing uses it again), taking the file's handle, call permission and the
writer's half out of `kdDmuInv`. What it returns is the start resource of the same generation
(`kvStart`, `BootLemmas.lean`, at the same file invariant `kdFileInvK γ id fl`): what `StartNode`'s
`start` takes, so the process starts the next incarnation from it (`Node.restart`).
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Defs
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.BootLemmas

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

/-- See the file header. -/
abbrev Replica.stop.spec : Prop :=
  ∀ (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (r : Loc),
  {{ repStopper (GF := GF) γ vs dir id r }}
    (App (Val (r @!! go.GoType.PointerType kReplicaTy @!! go!"stop")) (Val #()))
  {{ RET #(); ∃ (fl : KdFileNames) (qc : Qp), kvStart γ vs dir id fl qc }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
