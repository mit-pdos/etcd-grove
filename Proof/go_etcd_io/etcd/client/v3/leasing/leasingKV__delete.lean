/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__delete.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__delete
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__waitSession
public import Spec.go_etcd_io.etcd.client.v3.Op__RangeBytes
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__deleteRange
public import Spec.go_etcd_io.etcd.client.v3.Op__KeyBytes
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__tryModifyOp
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__revoke
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__Evict
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.ResponseOp__GetResponseDeleteRange
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__Delete
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKVLemmas
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingDeleteLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leasingKV.delete.wp_proof
    (hWS : leasingKV.waitSession.spec (GF := GF) (hG := hG))
    (hRange : EtcdGrove.Op.RangeBytes.spec (GF := GF) (hG := hG))
    (hDR : leasingKV.deleteRange.spec (GF := GF) (hG := hG))
    (hKey : EtcdGrove.Op.KeyBytes.spec (GF := GF) (hG := hG))
    (hTry : leasingKV.tryModifyOp.spec (GF := GF) (hG := hG))
    (hRevoke : leasingKV.revoke.spec (GF := GF) (hG := hG))
    (hEv : leaseCache.Evict.spec (GF := GF) (hG := hG))
    (hGRD : EtcdGrove.ResponseOp.GetResponseDeleteRange.spec (GF := GF) (hG := hG))
    (hLD : leaseCache.Delete.spec (GF := GF) (hG := hG)) :
    leasingKV.delete.spec (GF := GF) (hG := hG) := by
  intro lkv γ pfx ctx cs opv o lo
  wp_start as ⟨#Hlkv, Hrd, #Hctx, #Hcc, #Hop, #Hlo, %Hot⟩
  have Htop : txnOpOf o = some (.delete o) := by simp [txnOpOf, Hot]
  ihave #Hlkv' := Hlkv
  iunfold isLeasingKV at Hlkv'
  icases Hlkv' with ⟨%cl, %kv, %lctx, %lcs, %cancel, %osl, %Hpfx, -, -, -, -, -, -, -, -,
    -, -, -, -, #Hcache, -⟩
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Hctx2 := Hctx
  iNamed Hctx2
  ihave #Hop' := Hop
  iunfold opFullAt at Hop'
  icases Hop' with ⟨#HopAt, -⟩
  ihave #Hpeek := leasingX_peek (GF := GF) lkv γ
  (try wp_auto)
  wp_apply (hWS lkv γ pfx ctx cs) $$ [$Hlkv $Hrd $Hctx] as %err0 ⟨Hrd, Hws⟩
  unfold sessionReadyQ
  icases Hws with (%Hne | ⟨%Heq, #Hsr, -⟩)
  · obtain ⟨e, rfl⟩ : ∃ e, err0 = GoInterface.ok e := by
      cases err0 with
      | nil => exact absurd rfl Hne
      | ok e => exact ⟨e, rfl⟩
    (try wp_auto)
    iapply HΦ
    iframe
    ileft; ipureintro; exact ⟨Hne, rfl⟩
  subst Heq
  (try wp_auto)
  wp_apply hRange $$ [$Hcv $op $HopAt] as %esl ⟨op, #He⟩
  (try wp_auto)
  wp_if_destruct
  · wp_apply (hDR lkv γ pfx ctx cs opv o lo) $$ [$Hlkv $Hrd $Hsr $Hctx $Hcc $Hop $Hlo]
      as %dr0 %err0 ⟨Hrd, Hres⟩
    (try wp_auto)
    iapply HΦ
    iframe
  wp_apply hKey $$ [$Hcv $op $Hop] as %ksl ⟨op, #Hk⟩
  wp_apply wp_bytes_to_string ksl o.key DFrac.discard $$ [$Hk] as -
  (try wp_auto)
  ihave IH : iprop(∃ drv : Loc, "dr" ∷ dr_ptr ↦ drv ∗ "Hrd" ∷ lkvReader lkv γ pfx ∗
      "op" ∷ op_ptr ↦ opv ∗ "ctx" ∷ ctx_ptr ↦ GoInterface.ok ctx ∗ "lkv" ∷ lkv_ptr ↦ lkv ∗
      "key" ∷ key_ptr ↦ o.key) $$ [dr Hrd op ctx lkv key]
  · iexists _; simp only [named]; iframe
  wp_for IH
  ihave #HErrU := HErr $$ %Broadcast.Unknown
  wp_apply HErrU as %cerr Hcerr
  cases cerr with
  | ok e =>
    rw [ite_eq_right (show GoInterface.ok e ≠ GoInterface.nil from fun h => by cases h)]
    icases Hcerr with ⟨#HPD, #HCC⟩
    (try wp_auto)
    simp only [goose_wp_simp_extra, Bool.false_eq_true, ↓reduceIte]
    (try wp_auto)
    ihave #HErrD := HErr $$ %Broadcast.Done
    wp_apply HErrD $$ [$HCC] as %cerr2 %Hcerr2
    iapply HΦ
    iframe
    ileft; ipureintro; exact ⟨Hcerr2, rfl⟩
  | nil =>
  (try wp_auto)
  simp only [goose_wp_simp_extra, ↓reduceIte]
  (try wp_auto)
  wp_apply (hTry lkv γ pfx ctx cs opv o (.delete o) lo) $$ [$Hlkv $Hctx $Hop $Hlo] as %resp1 %wc %err1 Htry
  · ipureintro; exact ⟨Htop, Or.inr Hot⟩
  (try wp_auto)
  wp_join iprop(∃ (resp : Loc) (err : GoInterface), "resp" ∷ resp_ptr ↦ resp ∗ "err" ∷ err_ptr ↦ err ∗
      "Hrd" ∷ lkvReader lkv γ pfx ∗ "ctx" ∷ ctx_ptr ↦ GoInterface.ok ctx ∗ "op" ∷ op_ptr ↦ opv ∗
      "lkv" ∷ lkv_ptr ↦ lkv ∗ "key" ∷ key_ptr ↦ o.key ∗ "wcp" ∷ wc_ptr ↦ wc ∗
      "Hres" ∷ (⌜err ≠ GoInterface.nil⌝ ∨
        (⌜err = GoInterface.nil⌝ ∗ (opCommitted lo (.delete o) resp ∨ notCommitted resp))) ∗
      "Hwc" ∷ (⌜wc = null⌝ ∨ waitcClose wc))
    at next with [resp err Hrd Htry ctx op lkv key wc]
    as ⟨%resp, %err, resp, err, Hrd, ctx, op, lkv, key, wcp, Hres, Hwc⟩
  · icases Htry with (⟨%Hr1, %Hw1⟩ | ⟨%He1, Hc1, Hw1⟩)
    · subst Hw1
      cases err1 with
      | ok e =>
        (try wp_auto)
        wp_apply (hRevoke lkv γ pfx ctx cs o.key opv o (.delete o) lo) $$ [$Hlkv $Hrd $Hctx $Hcc $Hop $Hlo]
          as %resp2 %err2 ⟨Hrd, Hr2⟩
        · ipureintro; exact Htop
        (try wp_auto)
        wp_join_done
        iexists resp2, err2
        iframe
        ileft; ipureintro; rfl
      | nil =>
        (try wp_auto)
        wp_apply (hRevoke lkv γ pfx ctx cs o.key opv o (.delete o) lo) $$ [$Hlkv $Hrd $Hctx $Hcc $Hop $Hlo]
          as %resp2 %err2 ⟨Hrd, Hr2⟩
        · ipureintro; exact Htop
        (try wp_auto)
        wp_join_done
        iexists resp2, err2
        iframe
        ileft; ipureintro; rfl
    · subst He1
      icases Hw1 with (%Hw1 | Hw1)
      · subst Hw1
        (try wp_auto)
        wp_apply (hRevoke lkv γ pfx ctx cs o.key opv o (.delete o) lo) $$ [$Hlkv $Hrd $Hctx $Hcc $Hop $Hlo]
          as %resp2 %err2 ⟨Hrd, Hr2⟩
        · ipureintro; exact Htop
        (try wp_auto)
        wp_join_done
        iexists resp2, err2
        iframe
        ileft; ipureintro; rfl
      · (try wp_auto)
        wp_if_destruct
        · (try wp_auto)
          wp_apply (hRevoke lkv γ pfx ctx cs o.key opv o (.delete o) lo) $$ [$Hlkv $Hrd $Hctx $Hcc $Hop $Hlo]
            as %resp2 %err2 ⟨Hrd, Hr2⟩
          · ipureintro; exact Htop
          (try wp_auto)
          wp_join_done
          iexists resp2, err2
          iframe
          ileft; ipureintro; rfl
        · (try wp_auto)
          wp_join_done
          iexists resp1, GoInterface.nil
          simp only [named]
          iframe
  icases Hres with (%Hne | ⟨%Heq, Hc⟩)
  · obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
      cases err with
      | nil => exact absurd rfl Hne
      | ok e => exact ⟨e, rfl⟩
    (try wp_auto)
    wp_apply (hEv (lkvLeases lkv) γ.lc pfx (leasingX lkv γ) (leasingSeen γ) o.key (fun _ => iprop(True)))
      $$ [$Hcache $Hpeek] as %rv -
    · iintro %st %t HX
      imod leasingX_step lkv γ st (st.evict o.key t) $$ HX with ⟨HX, -⟩
      imodintro; iframe
    (try wp_auto)
    wp_for_post
    iapply HΦ
    iframe
    ileft; ipureintro; exact ⟨Hne, rfl⟩
  subst Heq
  icases Hc with (Hc | Hc)
  · icases opCommitted_delete lo o resp $$ Hc with
      ⟨%r, %s, %hm, %hdr, %rsl, %p0, %w, %dr, %h0, %Hhm, #HH, #Hhf, HS, #HR, #Hrsl, %Hp0, #Hw,
        #Hdr, %Hdrn, Hh0, #Hdel, #Hr, %Hf, #Hts⟩
    (try wp_auto)
    ihave %Hlen := ownSlice_len _ _ _ $$ Hrsl
    have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z rsl.len := by
      simp only [List.length_singleton] at Hlen
      constructor <;> word
    rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
    wp_apply wp_load_slice_index rsl (sint.Z (W64 0)) [p0] _ p0 (by decide) $$ [Hrsl] as -
    · iframe #; ipureintro; rfl
    ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
    · iPkgInit
    wp_apply hGRD p0 w dr $$ [$Hpb $Hw $Hdr]
    · ipureintro; exact Hp0
    (try wp_auto)
    wp_apply (hLD (lkvLeases lkv) γ.lc pfx (leasingX lkv γ) (leasingSeen γ) o.key hdr hm
        (fun _ => iprop(True))) $$ [$Hcache $Hpeek $Hhf] as -
    · iintro %st %h' HX
      imod leasingX_step lkv γ st (st.modify o.key (fun en => en.del h' hm)) $$ HX with ⟨HX, -⟩
      imodintro; iframe
    (try wp_auto)
    wp_join iprop(wc_ptr ↦ wc) at (if: _ then _ else _) with [Hwc wcp] as wcp
    · icases Hwc with (%Hwn | Hwc)
      · subst Hwn; (try wp_auto); wp_join_done; (try iframe)
      · wp_if_destruct
        · (try wp_auto); wp_join_done; (try iframe)
        · unfold waitcClose
          icases Hwc with ⟨%γch, Hwc⟩
          (try wp_auto)
          wp_apply wp_broadcast_chan_close $$ [$Hwc] as -
          · unfold waitQ; imodintro; itrivial
          (try wp_auto); wp_join_done; (try iframe)
    (try wp_auto)
    wp_for_post
    iapply HΦ
    iframe
    iright
    isplitr
    · ipureintro; rfl
    unfold deleteCommitted
    iexists r, s, hdr, hm, (rangeIn s o).length
    iframe
    iframe #
    ipureintro
    exact ⟨⟨Hdrn, Hhm, rfl⟩, Hf⟩
  · unfold notCommitted
    (try wp_auto)
    wp_join iprop(wc_ptr ↦ wc) at (if: _ then _ else _) with [Hwc wcp] as wcp
    · icases Hwc with (%Hwn | Hwc)
      · subst Hwn; (try wp_auto); wp_join_done; (try iframe)
      · wp_if_destruct
        · (try wp_auto); wp_join_done; (try iframe)
        · unfold waitcClose
          icases Hwc with ⟨%γch, Hwc⟩
          (try wp_auto)
          wp_apply wp_broadcast_chan_close $$ [$Hwc] as -
          · unfold waitQ; imodintro; itrivial
          (try wp_auto); wp_join_done; (try iframe)
    (try wp_auto)
    wp_for_post
    iframe
    iexists _
    simp only [named]
    iframe

end proof

end leasing
end EtcdGrove
end Perennial
