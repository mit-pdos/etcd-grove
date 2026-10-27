/-
Lemmas of the role step functions (`stepFollower`, `stepCandidate`, `stepLeader`) for the raft
v3.7 retarget (stage R4, phase 3, group G3).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The two voter halves of the tracker at `c` (2026-10-14, reconfiguration stage A3), as the
`quorum`/`readOnly` methods take them (`ownIdsetQ`), with their size bounds; given back
unchanged. -/
theorem ownTrackerC_halves (c : CfgM) (tv : tracker.ProgressTracker) (t : Trk) :
    ⊢ ownTrackerC (GF := GF) c tv t -∗
      ∃ (vin vout : Loc), ⌜tv.Config'.Voters'.arr = [vin, vout]⌝ ∗
        ⌜(GMap.size c.incoming : Int) ≤ 2 ^ 62 ∧ (GMap.size c.outgoing : Int) ≤ 2 ^ 62⌝ ∗
        ownIdsetQ vin (DFrac.own 1) c.incoming ∗ ownIdsetQ vout (DFrac.own 1) c.outgoing ∗
        (ownIdsetQ vin (DFrac.own 1) c.incoming -∗ ownIdsetQ vout (DFrac.own 1) c.outgoing -∗
           ownTrackerC c tv t) := by
  obtain ⟨votes, prs, pvs, ep⟩ := t
  iintro Hown
  icases ownTrackerC_voters_size c tv _ $$ Hown with ⟨%Hsz, Hown⟩
  iunfold ownTrackerC at Hown
  iNamed Hown
  icases ownCfgCC_voters _ _ $$ Hcfg with ⟨%vin, %vout, %Harr, Hv0, Hv1, Hcback⟩
  iexists vin, vout
  isplitr
  · ipureintro; exact Harr
  isplitr
  · ipureintro; exact ⟨Hsz.2.1, Hsz.2.2⟩
  iframe Hv0 Hv1
  iintro Hv0 Hv1
  ihave Hcfg := Hcback $$ Hv0 Hv1
  iapply ownTrackerC_intro c tv votes prs pvs Hinv Hdom Hflags Hsize HmaxInfl Hnw
    $$ Hvotes Hprs Hprogs Hcfg Hepoch

/-! ### The `Entries` field of a message, held apart (`stepLeader`'s `MsgProp` loop)

v3.7's conf-change loop ranges over `m.GetEntries()` and calls `m.GetEntries()` again in its
body (to read entry `i`, and to overwrite a refused slot). `GetEntries`' spec lends the slice
and takes it back, so it cannot relate two calls' slices; the loop instead holds the field
apart (`msgPtsC_acc_entries`) and reads it through the getter's body
(`wp_Message_GetEntries_field`), so every call returns the same slice. -/

/-- The `Entries` field out of a message, the rest kept closed. -/
theorem msgPtsC_acc_entries (l : Loc) (dq dqe : DFrac) (cap : Bool) (ms : MsgSt) :
    msgPtsC (GF := GF) l dq dqe cap ms ⊢
      ∃ (es : GoSlice) (els : List Loc),
        ⌜l ≠ null⌝ ∗
        l.[raftpb.Message, go!"Entries"] ↦{dq} es ∗ es ↦*{dqe} els ∗
        ([∗list] p;e ∈ els;ms.ents, entRO p e) ∗
        (if cap then ownSliceCap Loc es (DFrac.own 1) else emp) ∗
        (∀ (els' : List Loc) (ents' : List EntryM) (cap' : Bool),
          l.[raftpb.Message, go!"Entries"] ↦{dq} es -∗ es ↦*{dqe} els' -∗
          ([∗list] p;e ∈ els';ents', entRO p e) -∗
          (if cap' then ownSliceCap Loc es (DFrac.own 1) else emp) -∗
          msgPtsC l dq dqe cap' { ms with ents := ents' }) := by
  iintro H
  iNamed H
  iexists es, els
  isplitr
  · ipureintro; exact Hnn
  iframe HEs Hes Hents Hes_cap
  iintro %els' %ents' %cap' HEs Hes #Hents' Hes_cap
  iunfold msgPtsC
  iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els', ps, cs, rs, uf
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hents' Hcs Hpb

/-- `m.GetEntries()` on the field alone, from the getter's body (a nil check and a load). -/
theorem wp_Message_GetEntries_field (l : Loc) (dq : DFrac) (es : GoSlice) (Hnn : l ≠ null) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb ∗
        l.[raftpb.Message, go!"Entries"] ↦{dq} es }}
      (App (Val (l @!! go.GoType.PointerType raftpb.Message.ty @!! go!"GetEntries")) (Val #()))
    {{ RET #es; l.[raftpb.Message, go!"Entries"] ↦{dq} es }} := by
  wp_start as HEs
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  · iapply HΦ
    iframe HEs

/-- A `*pb.ConfChangeV2`'s `Changes` field, lent (`len(cc.AsV2().Changes)`), with the number of
changes it holds. -/
theorem ownCCV2_changes (p : Loc) (dq : DFrac) (m : CCV2M) :
    ownCCV2 (GF := GF) p dq m ⊢
      ∃ (chs : GoSlice), p.[raftpb.ConfChangeV2, go!"Changes"] ↦{dq} chs ∗
        ⌜m.changes.length = sint.nat chs.len ∧ 0 ≤ sint.Z chs.len⌝ ∗
        (p.[raftpb.ConfChangeV2, go!"Changes"] ↦{dq} chs -∗ ownCCV2 p dq m) := by
  iintro H
  iNamed H
  ihave %Hl1 := ownSlice_len _ _ _ $$ Hch
  ihave %Hl2 := BigSepL2.bigSepL2_length $$ Hccs
  iexists chs
  iframe HCh
  isplitr
  · ipureintro; exact ⟨by rw [← Hl2]; exact Hl1.1, Hl1.2⟩
  iintro HCh
  iunfold ownCCV2
  iexists pt, chs, ls, cs, uf
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cT Hccs Hcs Hpb

/-- The struct `&pb.Entry{Type: pb.EntryNormal.Enum()}` allocates, its `Type` cell at `pty`. -/
abbrev normalEntryV (pty : Loc) : raftpb.Entry :=
  { state' := zeroValDef, Term' := null, Index' := null, Type' := pty, Data' := slice.nil,
    Subterm' := null, unknownFields' := slice.nil, sizeCache' := 0 }

/-- `&pb.Entry{Type: pb.EntryNormal.Enum()}` (`stepLeader`'s refused conf change): a fresh entry
whose `Type` cell holds `EntryNormal` and whose other fields are unset, frozen, holds the zero
record. -/
theorem entRO_normal_of_struct (l pty : Loc) (v : raftpb.Entry) (E : CoPset)
    (HT : v.Term' = null) (HI : v.Index' = null) (HY : v.Type' = pty) (HD : v.Data' = slice.nil)
    (HS : v.Subterm' = null) (Hu : v.unknownFields' = slice.nil) :
    (l ↦ v ∗ pty ↦ (W32 0 : raftpb.EntryType) : IProp GF) ⊢ |={E}=> entRO l (zero_val EntryM) := by
  iintro ⟨Hl, Hty⟩
  imod cellRO_alloc $$ Hty with #cY
  ihave #cT : cellRO (GF := GF) v.Term' (zero_val EntryM).Term' $$ []
  · rw [HT]; iapply cellRO_null
  ihave #cI : cellRO (GF := GF) v.Index' (zero_val EntryM).Index' $$ []
  · rw [HI]; iapply cellRO_null
  ihave #Hd : (v.Data' ↦*□ (zero_val EntryM).Data' : IProp GF) $$ []
  · rw [HD]; iapply ownSlice_nil
  ihave #cS : cellRO (GF := GF) v.Subterm' (zero_val EntryM).Subterm' $$ []
  · rw [HS]; iapply cellRO_null
  imod entOwn_of_struct l v (zero_val EntryM) E Hu $$ [Hl] with Ho
  · iframe Hl
    iframe cT cI Hd cS
    rw [HY, show (zero_val EntryM).Type' = (W32 0 : raftpb.EntryType) from rfl]; iexact cY
  imod entOwn_freeze $$ Ho with #Ho
  imodintro
  iexact Ho

end proof

end EtcdGrove
end Perennial
