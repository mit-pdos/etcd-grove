/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/txWriteBuffer__putSeq.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.txWriteBuffer__putSeq
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.txWriteBuffer__putInternal
public import Spec.go_etcd_io.etcd.client.pkg.v3.verify.Verify
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.WBufLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

theorem backend.txWriteBuffer.putSeq.wp_proof
    (hVerify : verify.Verify.spec (GF := GF) (hG := hG))
    (hPutInternal : backend.txWriteBuffer.putInternal.spec (GF := GF) (hG := hG)) :
    backend.txWriteBuffer.putSeq.spec (GF := GF) (hG := hG) := by
  intro txw W b bi k v kb vb Hlen Hgt
  wp_start as ⟨HW, #Hb, #Hk, #Hv⟩
  unfold ownWB
  icases HW with ⟨%m, %s, Hbk, Hseq, Hbks, Hs⟩
  ihave #Hb' := Hb
  iunfold isBucket at Hb
  icases Hb with ⟨%bo, %Hbo, #HID, #-, #-⟩
  subst Hbo
  wp_auto
  wp_func_lits
  wp_apply (hVerify _ _ iprop(txw_ptr ↦ txw ∗ bucket_ptr ↦ GoInterface.ok bo ∗ k_ptr ↦ k ∗
      structFieldRef txWriteBuffer go!"txBuffer" txw ↦ ({ buckets' := m } : txBuffer) ∗
      ownBks m W.bks)) $$ [txw bucket k Hbk Hbks] as ⟨txw, bucket, k, Hbk, Hbks⟩
  · iframe txw bucket k Hbk Hbks
    iintro ⟨txw, bucket, k, Hbk, Hbks⟩
    icases ownBks_open m W.bks $$ Hbks with ⟨%M, Hm, Hbks⟩
    ihave %Hdom := bksOwn_dom M W.bks $$ Hbks
    wp_auto
    wp_apply HID
    wp_apply wp_map_lookup2 $$ Hm as Hm
    cases hM : M !! bi.id with
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, decide_false, Bool.not_false]
      wp_auto
      iexists _
      isplitr
      · ipureintro; rfl
      iframe txw bucket k Hbk
      iapply ownBks_close
      iframe Hm Hbks
    | some bb =>
      obtain ⟨es, hB⟩ := bksOwn_some Hdom hM
      simp only [Option.isSome_some, _root_.decide_true, Option.getD_some]
      icases bksOwn_acc hM hB $$ Hbks with ⟨Hbb, Hback⟩
      iunfold ownBB at Hbb
      icases Hbb with ⟨%p, Hbb, %Hok⟩
      iunfold bbAt at Hbb
      icases Hbb with ⟨Hbb, Hsl, Hcap, #Hro, #Hin⟩
      have hlenB : es.length < bufBound := by unfold bkOf at Hlen; rw [hB] at Hlen; exact Hlen
      have hes : bkOf W.bks bi.id = es := by unfold bkOf; rw [hB]; rfl
      rw [hes] at Hgt
      wp_auto
      by_cases Hif : (W64 es.length : w64) = W64 0
      · rw [_root_.decide_eq_true Hif]
        wp_auto
        ihave Hbks := Hback $$ %es [Hbb Hsl Hcap]
        · iunfold ownBB
          iexists p
          iunfold bbAt
          iframe Hbb Hsl Hcap Hro Hin
          ipureintro; exact Hok
        rw [GMap.insert_id _ _ _ hB]
        iexists _
        isplitr
        · ipureintro; rfl
        iframe txw bucket k Hbk
        iapply ownBks_close
        iframe Hm Hbks
      · rw [_root_.decide_eq_false Hif]
        ihave %Hsllen := ownSlice_len _ _ _ $$ Hsl
        have hpos : 0 < es.length := by
          unfold bufBound at hlenB
          rcases Nat.eq_zero_or_pos es.length with h | h
          · exact absurd (by rw [h]; rfl) Hif
          · exact h
        unfold bbOk at Hok
        wp_auto
        have hi : sint.Z (W64 es.length - W64 1) = (es.length : Int) - 1 := by
          unfold bufBound at hlenB; word
        rw [hi]
        simp only [show (0 ≤ (es.length : Int) - 1 ∧ (es.length : Int) - 1 < sint.Z p.buf.len) = True
          from eq_true (by constructor <;> word), ↓reduceIte]
        list_elem p.kvs (es.length - 1) as x
        list_elem es (es.length - 1) as e
        icases ownSlice_elem_acc ((es.length : Int) - 1) x p.buf _ p.kvs (by word)
          (by rw [show ((es.length : Int) - 1).toNat = es.length - 1 by omega]; exact Hx_lookup) $$ Hsl
          with ⟨Hx, Hsl⟩
        wp_auto
        ihave Hsl := Hsl $$ %x Hx
        rw [show ((es.length : Int) - 1).toNat = es.length - 1 by omega,
          list_set_lookup_self _ _ _ Hx_lookup]
        ihave #Hin' := Hin
        iunfold entsIn at Hin
        icases Hin with ⟨%-, #Hzip⟩
        ihave #Hxk := BigSepL.bigSepL_lookup (i := es.length - 1) (x := (x, e))
          (by rw [List.getElem?_zip_eq_some]; exact ⟨Hx_lookup, He_lookup⟩) $$ Hzip
        simp only
        icases Hxk with ⟨#Hxk, #-⟩
        wp_apply (bytes.wp_Compare k x.key' DFrac.discard DFrac.discard kb e.1) $$ [$Hk $Hxk] as ⟨-, -⟩
        have hgt : strLt e.1 kb := Hgt e (List.mem_of_getElem? He_lookup)
        have hcmp : bytes.compareResult kb e.1 = W64 1 := by
          unfold bytes.compareResult
          have hne : ¬ kb = e.1 := fun h => strLt_irrefl kb (by rw [h] at hgt ⊢; exact hgt)
          simp only [strLt_asymm hgt, hne, ↓reduceIte]
        rw [hcmp]
        wp_auto
        ihave Hbks := Hback $$ %es [Hbb Hsl Hcap]
        · iunfold ownBB
          iexists p
          iunfold bbAt
          iframe Hbb Hsl Hcap Hro Hin'
          ipureintro; exact Hok
        rw [GMap.insert_id _ _ _ hB]
        iexists _
        isplitr
        · ipureintro; rfl
        iframe txw bucket k Hbk
        iapply ownBks_close
        iframe Hm Hbks
  wp_apply (hPutInternal txw W _ bi k v kb vb Hlen) $$ [Hbk Hseq Hbks Hs] as HW
  · iframe Hb' Hk Hv
    unfold ownWB
    iexists m, s
    iframe
  unfold ownWB
  simp only [WBuf.putSeq]
  iapply HΦ $$ HW

end proof

end EtcdGrove
end Perennial
