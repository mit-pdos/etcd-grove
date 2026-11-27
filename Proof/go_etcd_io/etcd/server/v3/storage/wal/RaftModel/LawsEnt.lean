/-
**The raftpb instance's entry laws** (W4c U4 b of `notes/wal-fsext-w4c-plan.md`, "W4c U4 log"):
`WalPbIn.GetIndexLaw`, `GetTermLaw` (the getters over the frozen canonical entry), `MarshalEntLaw`
(`pbutil.MustMarshalMessage`, over the part's `proto.MarshalPb.spec` at the registered `pbEntryC`,
`pbEntryC_reg`) and `UnmarshalEntLaw` (`MustUnmarshalEntry`, `decoder.go`: `pbutil.MustUnmarshalMessage`
into a fresh entry, over `proto.UnmarshalPb.spec`; the bytes the decoder reads are the canonical
entry's encoding, `walDecEnt_small`, the stand-in bytes being longer than any slice). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.Getters
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__saveEntry
public import Spec.google_golang_org.protobuf.proto.MarshalPb
public import Spec.google_golang_org.protobuf.proto.UnmarshalPb
public import Spec.google_golang_org.protobuf.proto.SizePb
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__Save

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 WalEnc WalFs

section pure
variable [GooseExts]

/-- A canonical entry's encoding is not empty (its `Term` is set). -/
theorem entrySize_canon_pos (e : EntryM) : 0 < entrySize (walEntCanon e) := by
  unfold entrySize walEntCanon optVarintSize
  simp only [Option.map_some]
  omega

end pure

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- **`GetIndexLaw`.** -/
theorem walRaftP_getIndex : WalPbIn.GetIndexLaw (walRaftP (GF := GF)) := by
  intro l e
  rw [show (walRaftP (GF := GF)).entIn = walEntIn from rfl]
  wp_start_folded as #He
  unfold walEntIn
  icases He with ⟨#Hc, -⟩
  wp_apply (wp_entRoC_GetIndex l (walEntCanon e)) $$ []
  · iexact Hc
  simp only [walEntCanon_index, Option.getD]
  iapply HΦ; ipureintro; trivial

/-- **`GetTermLaw`.** -/
theorem walRaftP_getTerm : WalPbIn.GetTermLaw (walRaftP (GF := GF)) := by
  intro l e
  rw [show (walRaftP (GF := GF)).entIn = walEntIn from rfl]
  wp_start_folded as #He
  unfold walEntIn
  icases He with ⟨#Hc, -⟩
  wp_apply (wp_entRoC_GetTerm l (walEntCanon e)) $$ []
  · iexact Hc
  simp only [walEntCanon_term, Option.getD]
  iapply HΦ; ipureintro; trivial

/-- **`MarshalEntLaw`**, over `proto.Marshal`'s trust-boundary spec at the registered `raftpb.Entry`. -/
theorem walRaftP_marshalEnt (wp_Marshal : proto.MarshalPb.spec (GF := GF) (hG := hG)) :
    WalPbIn.MarshalEntLaw (walRaftP (GF := GF)) walRaftMr := by
  intro l e
  simp only [walRaftP]
  wp_start as #He
  unfold walEntIn
  icases He with ⟨#Hro, %Hs⟩
  obtain ⟨henc, -, hlen⟩ := walEncEnt_small Hs
  wp_auto
  have wpM := wp_Marshal pbEntryC pbEntryC_reg l (walEntCanon e) trivial Hs
  simp only [pbEntryC_ty, pbEntryC_roC, pbEncC_pbEntryC] at wpM
  wp_apply wpM $$ [] as %d ⟨Hd, Hcap, -⟩
  · iframe #
  (try wp_auto)
  ihave %Hlen := ownSlice_len _ _ _ $$ Hd
  iapply HΦ
  simp only [walRaftMr]
  rw [henc]
  iframe
  ipureintro
  rintro rfl
  have h0 := entrySize_canon_pos e
  rw [← hlen, henc, Hlen.1] at h0
  simp [slice.nil] at h0

/-- **`SizeLaw`** (`Save`'s pre-lock check, fix 0009), over `proto.Size`'s trust-boundary spec at the
registered `raftpb.Entry`. -/
theorem walRaftP_size (wp_Size : proto.SizePb.spec (GF := GF) (hG := hG)) :
    WalPbIn.SizeLaw (walRaftP (GF := GF)) walRaftMr := by
  intro l e
  rw [show (walRaftP (GF := GF)).entIn = walEntIn from rfl]
  wp_start_folded as #He
  iunfold walEntIn at He
  icases He with ⟨#Hro, %Hs⟩
  obtain ⟨henc, -, hlen⟩ := walEncEnt_small Hs
  have wpS := wp_Size pbEntryC pbEntryC_reg l (walEntCanon e)
  simp only [pbEntryC_ty, pbEntryC_roC, pbEntryC_size] at wpS
  wp_apply wpS $$ [] as %n %Hn
  · iframe #
  iapply HΦ
  ipureintro
  simp only [walRaftMr]
  rw [hlen]
  exact Hn

/-- **`pbutil.MustUnmarshalMessage(e, d)` into a fresh `raftpb.Entry`, of a canonical entry's bytes**:
the entry holds it, owned. -/
theorem wp_MustUnmarshalMessage_ent (wp_Unmarshal : proto.UnmarshalPb.spec (GF := GF) (hG := hG))
    (l : Loc) (d : GoSlice) (dq : DFrac) (e : EntryM) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil ∗
        (l ↦ (zero_val go_etcd_io.raft.v3.raftpb.Entry) : IProp GF) ∗
        d ↦*{dq} entryEncC (walEntCanon e) }}
      (App (App (Val (@! go_etcd_io.etcd.pkg.v3.pbutil.MustUnmarshalMessage))
        (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.raft.v3.raftpb.Entry.ty) #l)))
        (Val #d))
    {{ RET #(); d ↦*{dq} entryEncC (walEntCanon e) ∗ entPtsCC l (DFrac.own 1) (walEntCanon e) }} := by
  wp_start as ⟨Hb, Hd⟩
  wp_auto
  have wpU := wp_Unmarshal pbEntryC pbEntryC_reg d (entryEncC (walEntCanon e)) dq l
  simp only [pbEntryC_ty] at wpU
  wp_apply wpU $$ [Hd Hb] as %err ⟨Hd, %Hok, Hdec⟩
  · iframe; simp only [pbEntryC, pbEntryM]; iexact Hb
  have hu : (pbEntryC (GF := GF)).data.ufValid (walEntCanon e) := by
    simp only [pbEntryC_ufValid, walEntCanon_uf]
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact ufWire_nil _
  have he : err = GoInterface.nil := Hok ⟨walEntCanon e, trivial, hu, rfl⟩
  subst he
  wp_auto
  ihave ⟨%c, Hm, %Hc⟩ := Hdec $$ %rfl
  obtain ⟨-, -, -, Heq⟩ := Hc
  have h0 := Heq (walEntCanon e) trivial hu rfl
  subst h0
  iapply HΦ
  iframe

/-- **`UnmarshalEntLaw`**, over `proto.Unmarshal`'s trust-boundary spec at the registered
`raftpb.Entry`. -/
theorem walRaftP_unmarshalEnt (wp_Unmarshal : proto.UnmarshalPb.spec (GF := GF) (hG := hG)) :
    WalPbIn.UnmarshalEntLaw (walRaftP (GF := GF)) walRaftU := by
  intro d dq bs e hdec
  simp only [walRaftP]
  wp_start as Hd
  ihave %Hlen := ownSlice_len _ _ _ $$ Hd
  obtain ⟨hs, hbs⟩ := walDecEnt_small hdec (by rw [Hlen.1]; word)
  subst hbs
  iapply wp_fupd
  wp_auto
  wp_apply (wp_MustUnmarshalMessage_ent wp_Unmarshal _ d dq e) $$ [Hd e] as ⟨Hd, He⟩
  · iframe
  imod entPtsCC_freeze _ _ _ $$ He with #He
  imodintro
  iapply HΦ
  iframe Hd
  unfold walEntIn
  iframe He
  ipureintro; exact hs

end laws

end EtcdGrove
end Perennial
