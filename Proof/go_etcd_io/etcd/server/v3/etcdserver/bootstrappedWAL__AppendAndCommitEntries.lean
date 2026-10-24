/-
Proof of `(*bootstrappedWAL).AppendAndCommitEntries(ents)`
(`Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrappedWAL__AppendAndCommitEntries.lean`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrappedWAL__AppendAndCommitEntries

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxHeartbeats 0 in
theorem bootstrappedWAL.AppendAndCommitEntries.wp_proof :
    bootstrappedWAL.AppendAndCommitEntries.spec (GF := GF) := by
  intro w bw ents dq hs es entsM Hlen_bound
  wp_start as Hpre
  iNamed Hpre
  iunfold entsPts at Hents
  icases Hents with ⟨%ls1, Hs1, #Hb1⟩
  iunfold entsPts at Harg
  icases Harg with ⟨%ls2, Hs2, #Hb2⟩
  ihave %Heq1 := entsBig_length _ _ $$ Hb1
  ihave %Heq2 := entsBig_length _ _ $$ Hb2
  ihave #Hwalpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_slice_append (V := Loc) $$ [$Hs1 $Hcap $Hs2] as %ents' ⟨Hs', Hcap', Hs2⟩
  (try wp_auto)
  -- Freeze the freshly allocated `&raftpb.HardState{}` for `wal.w.Save`
  ihave #Hc0 : cellRO (GF := GF) (null : Loc) (W64 0) $$ []
  · rw [show (W64 0) = zero_val w64 from rfl]
    iapply cellRO_null
  imod hsRO_of_struct «$a0_ptr» (zero_val raftpb.HardState) (HardStateM.mk (W64 0) (W64 0) (W64 0))
    ⊤ rfl $$ [«$a0»] with #Hhst
  · iframe «$a0» Hc0
  ihave Harg : entsPts ents dq entsM $$ [Hs2]
  · iunfold entsPts; iexists ls2; iframe Hs2 Hb2
  iunfold bootWalSaveOk at Hsave
  wp_apply Hsave $$ %«$a0_ptr» %ents %dq %entsM [$Hhst $Harg] as Harg
  (try wp_auto)
  ihave %Hlen' := ownSlice_len _ _ _ $$ Hs'
  ihave #Hb' := entsBig_app ls1 ls2 es entsM $$ [$Hb1 $Hb2]
  have Hlen_eq : (es ++ entsM).length = (ls1 ++ ls2).length := by
    simp [Heq1, Heq2]
  wp_if_destruct
  · -- `ents'.len = W64 0` (`len(wal.ents) == 0`)
    rename_i Hif
    have Hempty : es ++ entsM = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [Hlen_eq, Hlen'.1, Hif]
      rfl
    have Hafter : hsAfterAppend hs es entsM = hs := by
      unfold hsAfterAppend
      rw [Hempty]; rfl
    iapply HΦ
    rw [Hafter]
    iexists ents'
    iframe Hwal Hst Hcap' Harg
    iunfold entsPts
    iexists (ls1 ++ ls2)
    iframe Hs' Hb'
  · -- `ents'.len ≠ W64 0` (`len(wal.ents) != 0`)
    rename_i Hif
    have Hpos_z : 0 < sint.Z ents'.len := by
      have := Hlen'.2
      have : sint.Z ents'.len ≠ 0 := by
        intro h; apply Hif; word
      omega
    have Hpos_ls : 0 < (ls1 ++ ls2).length := by
      rw [Hlen'.1]; word
    have Hpos : 0 < (es ++ entsM).length := by
      rw [Hlen_eq]; exact Hpos_ls
    have Hidx_z : sint.Z (ents'.len - W64 1) = ((es ++ entsM).length - 1 : Nat) := by
      rw [Hlen_eq, Hlen'.1]; unfold sint.nat; word
    have Hidx_lt : sint.Z (ents'.len - W64 1) < sint.Z ents'.len := by word
    have Hidx_ge : 0 ≤ sint.Z (ents'.len - W64 1) := by omega
    obtain ⟨l_last, Hllast⟩ : ∃ l_last, (ls1 ++ ls2)[(es ++ entsM).length - 1]? = some l_last :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨e_last, Helast⟩ : ∃ e_last, (es ++ entsM)[(es ++ entsM).length - 1]? = some e_last :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have Hllast' : (ls1 ++ ls2)[(sint.Z (ents'.len - W64 1)).toNat]? = some l_last := by
      rw [Hidx_z]; simpa using Hllast
    simp only [Hidx_ge, Hidx_lt, _root_.and_self, ↓reduceIte]
    icases ownSlice_elem_acc (sint.Z (ents'.len - W64 1)) l_last _ _ _ Hidx_ge Hllast' $$ Hs'
      with ⟨Hll, Hs'_close⟩
    ihave #Hent : entRO l_last e_last $$ []
    · iapply (BigSepL2.bigSepL2_lookup Hllast Helast) $$ Hb'
    icases entRO_Index_acc l_last e_last $$ Hent with ⟨%pi, #HI, #HcI⟩
    icases hsPts_not_null bw.st' (DFrac.own 1) hs $$ Hst with ⟨%Hstnn, Hst⟩
    icases hsPts_Commit_acc bw.st' hs $$ Hst with ⟨%pc, HstC, Hst_close⟩
    (try wp_auto)
    ihave Hs' := Hs'_close $$ Hll
    rw [list_insert_id Hllast']
    ihave Hst := Hst_close $$ %pi %e_last.Index' HstC HcI
    have Hafter : hsAfterAppend hs es entsM = { hs with Commit' := e_last.Index' } := by
      unfold hsAfterAppend
      rw [List.getLast?_eq_getElem?, Helast]
    iapply HΦ
    rw [Hafter]
    iexists ents'
    iframe Hwal Hst Hcap' Harg
    iunfold entsPts
    iexists (ls1 ++ ls2)
    iframe Hs' Hb'

end proof

end EtcdGrove
end Perennial
