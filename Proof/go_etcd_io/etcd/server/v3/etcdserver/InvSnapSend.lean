/-
**The merged snapshot's sender** (D22 S-h, 2026-10-20; `notes/decisions.md`, "D22 S-h carried
out"): the vocabulary of the specs of `createMergedSnapshotMessage`, `newSnapshotReaderCloser` and
`sendMergedSnap` (`snapshot_merge.go`, `server.go`). Lean-first (no Rocq counterpart).

* `srvKVCommitOk kv RC RC'`, `srvBeSnapOk b RS RS' Qd`: the contracts of the two interface calls
  `createMergedSnapshotMessage` makes, `s.KV().Commit()` (mvcc's `WatchableKV`; since D22 S-l's sender items
  discharged from the proved `store.Commit`, `srvKVCommitOk_of_kv`) and `s.be.Snapshot()` (the backend's `Snapshot`, whose observation `Qd` of the
  committed data the caller chooses: `backend.Snapshot.spec`'s `Q`, `srvBeSnapOk_of_backend`). The
  caller (`applyAll`'s `msgSnapC` branch, live from S-l) discharges them; the resources they move
  (`RC`, `RS`: a write session's token, the backend's read token and open share, the observation's
  resource) are its own; `RS` comes from what `Commit()` gives back (`RC' -∗ RS`: the stored-index
  window, which `Commit()` opens and the snapshot's observation reads, D22, 2026-10-23,
  `SnapSendBranch.lean`).
* `mergedSt st c i t`: the raft message `st` with its snapshot replaced by the merged one (no
  data, metadata `(c, i, t)`): what `createMergedSnapshotMessage` writes into `m.Snapshot`.
* `mergedMsg mg ml rc` (persistent): `mg` is the `*snap.Message` `NewMessage` made of `ml` and
  `rc`, with its `TotalSize` field read-only and its `closeC` a bag channel carrying nothing
  (`sendMergedSnap` reads both).
* `msgOwn_store_Snapshot`: `m.Snapshot = snapshot` on an owned message (a `MsgSnap` a `Ready` hands
  out is owned: `readyDq`; since D22 S-l's sender items, 2026-10-22, the server keeps it owned,
  `rnSnapMsg`, through `rnReadyData` and `processMessages` into `msgSnapC`'s bag).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Net
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvSnapshot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`kv`'s `Commit()`** (see the file header): from `RC`, `RC'`. -/
def srvKVCommitOk (kv : GoInterface) (RC RC' : IProp GF) : IProp GF :=
  iprop(∃ ki : GoInterfaceOk, ⌜kv = GoInterface.ok ki⌝ ∗
    {{ RC }} (App (Val #(methods ki.ty go!"Commit" ki.v)) (Val #())) {{ RET #(); RC' }})

/-- **`b`'s `Snapshot()`** (see the file header): from `RS`, a snapshot open over some committed
`D` with `Qd D`, and `RS'`. -/
def srvBeSnapOk (b : GoInterface) (RS RS' : IProp GF) (Qd : backend.Data → Prop) : IProp GF :=
  iprop(∃ bi : GoInterfaceOk, ⌜b = GoInterface.ok bi⌝ ∗
    {{ RS }} (App (Val #(methods bi.ty go!"Snapshot" bi.v)) (Val #()))
    {{ (sp : Loc) (D : backend.Data),
        RET #(interface.mkOk
          (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.snapshot.ty) #sp);
        backend.snapOpen sp D ∗ RS' ∗ ⌜Qd D⌝ }})

/-- **The merged message's content** (see the file header). -/
def mergedSt (st : MsgSt) (c : ConfStateM) (i t : w64) : MsgSt :=
  { st with snap := some (SnapshotM.mk [] (SnapshotMetadataM.mk c i t)) }

/-- **A merged snapshot message** (persistent; see the file header). -/
def mergedMsg (mg ml : Loc) (rc : GoInterface) : IProp GF :=
  iprop(snap.msgIs mg ml rc ∗ ∃ (tsz : w64) (cc : Loc) (γc : ChanNames),
    structFieldRef _root_.Perennial.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message
      go!"TotalSize" mg ↦□ tsz ∗
    snap.msgCloseC mg cc ∗ isChanBag γc cc (V := Bool) (fun _ => iprop(True)))

instance mergedMsg_persistent (mg ml : Loc) (rc : GoInterface) :
    Persistent (mergedMsg (GF := GF) mg ml rc) := by
  unfold mergedMsg; infer_instance

variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `m.Snapshot = snapshot` on an owned message (as raft's `msgPtsC_store_From`): the field, and
the message back with the new snapshot once a fresh owned snapshot is stored. -/
theorem msgOwn_store_Snapshot (l : Loc) (ms : MsgSt) :
    msgOwn (GF := GF) l (DFrac.own 1) ms ⊢
      ∃ p : Loc, l.[raftpb.Message, go!"Snapshot"] ↦ p ∗
        (∀ (p' : Loc) (sn : SnapshotM), l.[raftpb.Message, go!"Snapshot"] ↦ p' -∗
          ownSnapM p' (DFrac.own 1) sn -∗ msgOwn l (DFrac.own 1) { ms with snap := some sn }) := by
  iintro H
  simp only [msgOwn, msgPts]
  iNamed H
  iexists ps
  iframe HSn
  iintro %p' %sn HSn Hsn'
  iunfold msgPtsC
  iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, p', cs, rs, uf
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hents Hcs Hpb
  simp only [snapOpt]
  iexact Hsn'

end defs

end EtcdGrove
end Perennial
