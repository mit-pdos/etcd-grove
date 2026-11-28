/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/SnapDefs.lean (241f27e).
-/
/-
(stage 3, snap) Predicates of the snapshot paths' internal specs: the counting reader
(`countingReaderIs`) and the restore monitor (`monitorOwn`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Perennial.Proof.sync.OnceDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.hashicorp.raft

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- (stage 3) `cr` is a `*countingReader` over the reader `rd` (persistent): its `reader` field
(read-only) and its byte count under its mutex. -/
def countingReaderIs (cr : Loc) (rd : GoInterface) : IProp GF :=
  iprop(cr.[countingReader, go!"reader"] ↦□ rd ∗
    sync.isMutex (cr.[countingReader, go!"mu"]) (∃ n : w64, cr.[countingReader, go!"bytes"] ↦ n))

instance countingReaderIs_persistent cr rd : Persistent (countingReaderIs (GF := GF) cr rd) := by
  unfold countingReaderIs; infer_instance

/-- (stage 3) A restore monitor `m` (`startSnapshotRestoreMonitor`), which `StopAndWait` stops
(persistent): its `cancel` function (callable, it makes the monitor goroutine's context done), its
`doneCh` (a broadcast channel the monitor goroutine closes as it exits), and its `once`. -/
def monitorOwn (m : Loc) : IProp GF :=
  iprop(∃ (cancel : GoFunc) (dch : Loc) (γd : ChanNames),
    m.[snapshotRestoreMonitor, go!"cancel"] ↦□ cancel ∗
    m.[snapshotRestoreMonitor, go!"doneCh"] ↦□ dch ∗
    sync.isOnce (m.[snapshotRestoreMonitor, go!"once"]) iprop(True) iprop(True) ∗
    (□ ∀ Φ : val → IProp GF, ▷ Φ #() -∗ WP (App (Val #cancel) (Val #())) {{ Φ }}) ∗
    ownBroadcastChan dch γd iprop(True) .Unknown)

instance ownBroadcastChan_Unknown_persistent (ch : Loc) (γ : ChanNames) (Q : IProp GF) :
    Persistent (ownBroadcastChan (GF := GF) ch γ Q .Unknown) := by
  rw [ownBroadcastChan_unseal]; unfold ownBroadcastChanDef; dsimp only; infer_instance

instance monitorOwn_persistent m : Persistent (monitorOwn (GF := GF) m) := by
  unfold monitorOwn; infer_instance

end defs

end github_com.hashicorp.raft

end Perennial
