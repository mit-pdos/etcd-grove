/-
**The merged snapshot's sender** (D22 S-h, 2026-10-20; `notes/decisions.md`, "D22 S-h carried
out"): the vocabulary of the specs of `createMergedSnapshotMessage`, `newSnapshotReaderCloser` and
`sendMergedSnap` (`snapshot_merge.go`, `server.go`). Lean-first (no Rocq counterpart).

* `srvKVCommitOk kv RC RC'`, `srvBeSnapOk b RS RS' Qd`: the contracts of the two interface calls
  `createMergedSnapshotMessage` makes, `s.KV().Commit()` (mvcc's `WatchableKV`; strict M1,
  2026-11-06: from the API's `KV.Commit.contract`, `srvKVCommitOk_of_kv`) and `s.be.Snapshot()`
  (whose observation `Qd D` of the committed data `D` the caller chooses; strict M1: a resource, in
  place of a pure fact, since the snapshot's image is mvcc's persistent `mvccImage` and the writer's
  half comes back with it: `mvccImage_snapshot.law` at the writer's update,
  `SnapSendBranch.mergedCreate_window`). The
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

/-- **`b`'s `Snapshot()`** (see the file header): from `RS` and a `threadTok` (the snapshot's
reader slot of bbolt's `mmaplock`, 2026-11-06, `notes/begin-tok-plan.md`: held until the snapshot's
`Close`), a snapshot open over some committed `D` with `Qd D`, and `RS'`. -/
def srvBeSnapOk (b : GoInterface) (RS RS' : IProp GF) (Qd : backend.Data → IProp GF) : IProp GF :=
  iprop(∃ bi : GoInterfaceOk, ⌜b = GoInterface.ok bi⌝ ∗
    {{ RS ∗ threadTok }} (App (Val #(methods bi.ty go!"Snapshot" bi.v)) (Val #()))
    {{ (sp : Loc) (D : backend.Data),
        RET #(interface.mkOk
          (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.snapshot.ty) #sp);
        backend.snapOpen sp D ∗ RS' ∗ Qd D }})

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

/-! ### The merged message at its content (raft-entsize [r3c], 2026-11-10)

The merged snapshot and metadata are fresh struct literals (`unknownFields` nil), so their contents
have no unknown fields; the raft message is a `MsgSnap` raft handed out, without top-level unknown
fields (`rnSnapMsg`'s `pbMsg … []`) and with no entries, `Context` or responses (`SentMsgShape`); the
conf state is a clone of the voters' (`csPts`: none, at most `2 ^ 20` ids). So the merged message's
content is of bounded size (`msgSizeOk`), hence below `2 ^ 47` bytes: the envelope encoder's bound
(`msgSzC False`, `netSnapBundle`'s). Kept here, not in raft's `InvPb`. -/

/-- A fresh `*pb.SnapshotMetadata` literal (hidden fields zero) at its content: no unknown fields;
its conf state's content without unknown fields. -/
theorem smPtsCC_of_struct (p : Loc) (v : raftpb.SnapshotMetadata) (md : SnapshotMetadataM)
    (E : CoPset) (Hu : v.unknownFields' = slice.nil) :
    (p ↦ v ∗ csOpt v.ConfState' (DFrac.own 1) md.ConfState' ∗ cellRO v.Index' md.Index' ∗
      cellRO v.Term' md.Term' : IProp GF) ⊢ |={E}=>
      ∃ m : SnapMetaC, smPtsCC p (DFrac.own 1) m ∗
        ⌜m.model = md ∧ m.uf = [] ∧ ∀ cs ∈ m.confState, cs.uf = []⌝ := by
  iintro ⟨Hp, Hc, #cI, #cT⟩
  ihave Hc := csOpt_csOptA _ _ _ $$ Hc
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨state, ConfState, Index, Term, unknownFields, sizeCache, -⟩
  rw [Hu]
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod pbMsg_alloc raftpb.SnapshotMetadata p v.state' v.sizeCache' slice.nil [] E (ufWire_nil _)
    $$ [state sizeCache unknownFields Hnil] with #Hpb
  · iframe
  ihave ⟨%oC, oC', %hC⟩ := csOptA_csOptCC v.ConfState' (DFrac.own 1) md.ConfState' $$ Hc
  ihave ⟨%oI, #oI', %hI⟩ := cellRO_optCell v.Index' md.Index' $$ cI
  ihave ⟨%oT, #oT', %hT⟩ := cellRO_optCell v.Term' md.Term' $$ cT
  imodintro
  iexists ⟨oC, oI, oT, []⟩
  isplitl
  · unfold smPtsCC
    iexists v.ConfState', v.Index', v.Term'
    isplitr
    · ipureintro; exact Hnn
    iframe ConfState oC' Index oI' Term oT' Hpb
  ipureintro
  refine ⟨?_, rfl, hC.2⟩
  obtain ⟨a, b, d⟩ := md
  simp only [SnapMetaC.model] at *
  rw [hC.1, hI, hT]

/-- A fresh `*pb.Snapshot` literal (hidden fields zero, `Data` nil) at its content: no data, the
metadata's content, no unknown fields. -/
theorem ownSnapCC_of_struct (p : Loc) (v : raftpb.Snapshot) (m : SnapMetaC) (E : CoPset)
    (Hu : v.unknownFields' = slice.nil) (Hd : v.Data' = slice.nil) :
    (p ↦ v ∗ smPtsCC v.Metadata' (DFrac.own 1) m : IProp GF) ⊢ |={E}=>
      ownSnapCC p (DFrac.own 1) ⟨none, some m, []⟩ := by
  iintro ⟨Hp, Hm⟩
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨state, Data, Metadata, unknownFields, sizeCache, -⟩
  rw [Hu]
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod pbMsg_alloc raftpb.Snapshot p v.state' v.sizeCache' slice.nil [] E (ufWire_nil _)
    $$ [state sizeCache unknownFields Hnil] with #Hpb
  · iframe
  imodintro
  unfold ownSnapCC
  iexists v.Data', v.Metadata'
  simp only [bytesCC, smOptCC]
  isplitr
  · ipureintro; exact Hnn
  iframe Data Metadata Hm Hpb
  ipureintro; exact Hd

/-- `m.Snapshot = snapshot` on an owned message at its content: the field, and the message back
at the content with the new snapshot. -/
theorem msgPtsCC_store_Snapshot (l : Loc) (dqe : DFrac) (cap : Bool) (c : MsgC) :
    msgPtsCC (GF := GF) l (DFrac.own 1) dqe cap c ⊢
      ∃ p : Loc, l.[raftpb.Message, go!"Snapshot"] ↦ p ∗
        (∀ (p' : Loc) (o : Option SnapC), l.[raftpb.Message, go!"Snapshot"] ↦ p' -∗
          snapOptCC p' (DFrac.own 1) o -∗
          msgPtsCC l (DFrac.own 1) dqe cap (MsgC.mk { c.f with snapshot := o } c.resps)) := by
  unfold msgPtsCC
  iintro ⟨%pty, %pto, %pfr, %pte, %plt, %pix, %pco, %pvo, %prj, %prh, %es, %els, %ps, %cs,
    %rsl, %Hnn, HTy, #cTy, HTo, #cTo, HFr, #cFr, HTe, #cTe, HLt, #cLt, HIx, #cIx, HCo, #cCo,
    HVo, #cVo, HRj, #cRj, HRh, #cRh, HEs, Hes, #Hents, Hcap, HSn, -, HCx, #Hcx, HRs, Hrs, #Hpb⟩
  iexists ps
  iframe HSn
  iintro %p' %o HSn Hsn
  simp only [MsgC.f, MsgC.resps]
  iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, p', cs, rsl
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hents Hcx Hpb

theorem repW64Size_le (xs : List w64) : repW64Size xs ≤ 11 * xs.length := by
  induction xs with
  | nil => simp [repW64Size]
  | cons x xs ih =>
    have := varintSize_le_ten (uint.Z x).toNat (by word)
    simp only [repW64Size, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    omega

/-- **The merged message's content is of bounded size**: no responses, entries, `Context` or own
unknown fields, and a snapshot without data or unknown fields whose conf state lists at most
`2 ^ 20` ids. -/
theorem merged_sizeOk (f : MsgFC) (m : SnapMetaC) (hr : f.entries = [])
    (hc : (f.context.getD []).length = 0) (hu : f.uf = []) (hmu : m.uf = [])
    (hcs : ∀ cs ∈ m.confState, cs.uf = [] ∧
      (cs.voters ++ cs.learners ++ cs.votersOutgoing ++ cs.learnersNext).length ≤ 2 ^ 20) :
    msgSizeOk (MsgC.mk { f with snapshot := some ⟨none, some m, []⟩ } []) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · have hms : metaSize m ≤ 2 ^ 27 := by
      have hI := optW64Size_le m.index
      have hT := optW64Size_le m.term
      unfold metaSize
      rcases hm : m.confState with _ | cs
      · simp only [hmu, List.length_nil]; omega
      · obtain ⟨hcu, hcl⟩ := hcs cs hm
        simp only [List.length_append] at hcl
        have := repW64Size_le cs.voters; have := repW64Size_le cs.learners
        have := repW64Size_le cs.votersOutgoing; have := repW64Size_le cs.learnersNext
        have hb : optBoolSize cs.autoLeave ≤ 2 := by
          rcases cs.autoLeave with _ | _ <;> simp [optBoolSize]
        have hs : csSize cs ≤ 11 * 2 ^ 20 + 2 := by
          simp only [csSize, hcu, List.length_nil]; omega
        have := lenSize_le (csSize cs)
        simp only [hmu, List.length_nil]; omega
    have := lenSize_le (metaSize m)
    simp only [hdrBytes, MsgC.f, optSnapSize, snapSize, optBytesSize, hu, List.length_nil]
    rw [hc]
    omega
  · simp [MsgC.f, hr]
  · simp [MsgC.f, hr]

end defs

end EtcdGrove
end Perennial
