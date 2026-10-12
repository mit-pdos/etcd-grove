/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__put.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__put
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__waitSession
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__tryModifyOp
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__revoke
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__Update
public import Spec.go_etcd_io.etcd.client.v3.Op__KeyBytes
public import Spec.go_etcd_io.etcd.client.v3.Op__ValueBytes
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.ResponseOp__GetResponsePut
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKVLemmas
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingPutLemmas
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseCacheLemmas

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
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leasingKV.put.wp_proof
    (hWS : leasingKV.waitSession.spec (GF := GF) (hG := hG))
    (hTry : leasingKV.tryModifyOp.spec (GF := GF) (hG := hG))
    (hKey : EtcdGrove.Op.KeyBytes.spec (GF := GF) (hG := hG))
    (hRevoke : leasingKV.revoke.spec (GF := GF) (hG := hG))
    (hVal : EtcdGrove.Op.ValueBytes.spec (GF := GF) (hG := hG))
    (hUpd : leaseCache.Update.spec (GF := GF) (hG := hG))
    (hGRP : EtcdGrove.ResponseOp.GetResponsePut.spec (GF := GF) (hG := hG)) :
    leasingKV.put.spec (GF := GF) (hG := hG) := by
  intro lkv γ pfx ctx cs opv o top lo
  wp_start as ⟨#Hlkv, Hrd, #Hctx, #Hcc, #Hop, #Hlo, %Hpre⟩
  obtain ⟨Hot, Htop⟩ := Hpre
  ihave #Hlkv' := Hlkv
  iunfold isLeasingKV at Hlkv'
  icases Hlkv' with ⟨%cl, %kv, %lctx, %lcs, %cancel, %osl, %Hpfx, #Hcl, #Hkvf, #Hpfxf, #Hctxf,
    #Hcan, #Hosl, #HKV, #HDo, #HTxn, #HLC, #Hlctx, #Hlcc, #Hcache, #Hwg, #Hwginv, %Hbound⟩
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Hctx2 := Hctx
  iNamed Hctx2
  (try wp_auto)
  wp_apply (hWS lkv γ pfx ctx cs) $$ [$Hlkv $Hrd $Hctx] as %err0 ⟨Hrd, Hws⟩
  icases Hws with (%Hne | ⟨%Heq, -⟩)
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
  ihave IH : iprop(∃ prv : Loc, "pr" ∷ pr_ptr ↦ prv ∗ "Hrd" ∷ lkvReader lkv γ pfx ∗
      "op" ∷ op_ptr ↦ opv ∗ "ctx" ∷ ctx_ptr ↦ GoInterface.ok ctx ∗ "lkv" ∷ lkv_ptr ↦ lkv) $$ [pr Hrd op ctx lkv]
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
  wp_apply (hTry lkv γ pfx ctx cs opv o top lo) $$ [$Hlkv $Hctx $Hop $Hlo] as %resp1 %wc %err1 Htry
  · ipureintro; exact ⟨Htop, Or.inl Hot⟩
  (try wp_auto)
  wp_join iprop(∃ (resp : Loc) (err : GoInterface), "resp" ∷ resp_ptr ↦ resp ∗ "err" ∷ err_ptr ↦ err ∗
      "Hrd" ∷ lkvReader lkv γ pfx ∗ "op" ∷ op_ptr ↦ opv ∗ "ctx" ∷ ctx_ptr ↦ GoInterface.ok ctx ∗
      "lkv" ∷ lkv_ptr ↦ lkv ∗ "wcp" ∷ wc_ptr ↦ wc ∗
      "Hres" ∷ (⌜err ≠ GoInterface.nil⌝ ∨
        (⌜err = GoInterface.nil⌝ ∗ (opCommitted lo top resp ∨ notCommitted resp))) ∗
      "Hwc" ∷ (⌜wc = null⌝ ∨ waitcClose wc))
    at next with [resp err Hrd Htry op ctx lkv wc]
    as ⟨%resp, %err, resp, err, Hrd, op, ctx, lkv, wcp, Hres, Hwc⟩
  · icases Htry with (⟨%Hr1, %Hw1⟩ | ⟨%He1, Hc1, Hw1⟩)
    · subst Hw1
      cases err1 with
      | ok e =>
        (try wp_auto)
        wp_apply hKey $$ [$Hcv $Hop] as %ksl #Hk
        wp_apply wp_bytes_to_string ksl o.key DFrac.discard $$ [$Hk] as -
        (try wp_auto)
        wp_apply (hRevoke lkv γ pfx ctx cs o.key opv o top lo) $$ [$Hlkv $Hrd $Hctx $Hcc $Hop $Hlo]
          as %resp2 %err2 ⟨Hrd, Hr2⟩
        · ipureintro; exact Htop
        (try wp_auto)
        wp_join_done
        iexists resp2, err2
        iframe
        ileft; ipureintro; rfl
      | nil =>
        (try wp_auto)
        wp_apply hKey $$ [$Hcv $Hop] as %ksl #Hk
        wp_apply wp_bytes_to_string ksl o.key DFrac.discard $$ [$Hk] as -
        (try wp_auto)
        wp_apply (hRevoke lkv γ pfx ctx cs o.key opv o top lo) $$ [$Hlkv $Hrd $Hctx $Hcc $Hop $Hlo]
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
        wp_apply hKey $$ [$Hcv $Hop] as %ksl #Hk
        wp_apply wp_bytes_to_string ksl o.key DFrac.discard $$ [$Hk] as -
        (try wp_auto)
        wp_apply (hRevoke lkv γ pfx ctx cs o.key opv o top lo) $$ [$Hlkv $Hrd $Hctx $Hcc $Hop $Hlo]
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
          wp_apply hKey $$ [$Hcv $Hop] as %ksl #Hk
          wp_apply wp_bytes_to_string ksl o.key DFrac.discard $$ [$Hk] as -
          (try wp_auto)
          wp_apply (hRevoke lkv γ pfx ctx cs o.key opv o top lo) $$ [$Hlkv $Hrd $Hctx $Hcc $Hop $Hlo]
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
    wp_for_post
    iapply HΦ
    iframe
    ileft; ipureintro; exact ⟨Hne, rfl⟩
  subst Heq
  icases Hc with (Hc | Hc)
  · icases opCommitted_put lo top resp (txnOpOf_put_kind Htop Hot) $$ Hc with
      ⟨%r, %s, %hm, %hdr, %rsl, %p0, %w, %pr, %h0, %Hhm, #HH, #Hhf, HS, #HR, #Hrsl, %Hp0, #Hw,
        #Hpr, %Hprn, Hh0, #Hr, %Hf, #Hts⟩
    subst Hhm
    (try wp_auto)
    ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
    · iPkgInit
    ihave #Hcache' := Hcache
    unfold lkvCache isLeaseCache
    icases Hcache' with ⟨#Hguard, #Hclch⟩
    wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hlk, HP⟩
    icases leaseCacheInv_open_w $$ HP with ⟨%st, Hown, HX, Hinst, Hready, #Hfacts, %Hwf, Hclose⟩
    wp_apply hKey $$ [$Hcv $Hop] as %ksl #Hk
    wp_apply hVal $$ [$Hcv $Hop] as %vsl #Hv
    (try wp_auto)
    wp_apply hUpd (lkvLeases lkv) st ksl o.key vsl o.val hdr hm $$ [$Hpkg $Hown $Hk $Hv $Hhf]
      as ⟨%pp, %sl', Hown⟩
    · ipureintro; exact Hwf
    imod leasingX_step (GF := GF) lkv γ st (st.modify o.key (fun e =>
      e.update (freshKv pp ksl o.key hm.revision) sl' hdr hm vsl o.val)) $$ HX with ⟨HX, #Hstep⟩
    have hli : ∀ e : LeaseEntry,
        (e.update (freshKv pp ksl o.key hm.revision) sl' hdr hm vsl o.val).li = e.li :=
      fun e => (update_fields e _ _ _ hm vsl o.val).1
    have hmo := modify_other o.key (fun e =>
      e.update (freshKv pp ksl o.key hm.revision) sl' hdr hm vsl o.val) st
    have hready : (st.modify o.key (fun e =>
        e.update (freshKv pp ksl o.key hm.revision) sl' hdr hm vsl o.val)).readyN = st.readyN := by
      unfold LeaseCacheSt.readyN; rw [hmo.1]
    ihave #Hfacts' := modify_facts pfx o.key (fun e =>
      e.update (freshKv pp ksl o.key hm.revision) sl' hdr hm vsl o.val) st (fun e =>
        let h := update_fields e (freshKv pp ksl o.key hm.revision) sl' hdr hm vsl o.val
        ⟨h.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩) $$ Hfacts
    imod Hclose $$ %_ %(modify_wf o.key _ st hli Hwf) Hfacts' [Hinst] [Hready] Hown HX with HP
    · rw [hmo.2.2.2.2.2.2]; iexact Hinst
    · rw [hready]; iexact Hready
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hlk $HP]
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
    wp_apply hGRP p0 w pr $$ [$Hpb $Hw $Hpr]
    · ipureintro; exact Hp0
    (try wp_auto)
    icases Hwc with (%Hwn | Hwc)
    · subst Hwn
      (try wp_auto)
      wp_for_post
      iapply HΦ
      iframe
      iright
      isplitr
      · ipureintro; rfl
      unfold putCommitted
      iexists hm.revision, s, hdr, hm
      iframe
      iframe #
      isplitr
      · ipureintro; exact ⟨Hprn, rfl⟩
      isplitr
      · ipureintro; exact Hf.1
      isplitr
      · ipureintro; exact Hf.2.1
      isplitr
      · ipureintro; exact Hf.2.2.1
      ipureintro; exact Hf.2.2.2
    · wp_if_destruct
      · (try wp_auto)
        wp_for_post
        iapply HΦ
        iframe
        iright
        isplitr
        · ipureintro; rfl
        unfold putCommitted
        iexists hm.revision, s, hdr, hm
        iframe
        iframe #
        isplitr
        · ipureintro; exact ⟨Hprn, rfl⟩
        isplitr
        · ipureintro; exact Hf.1
        isplitr
        · ipureintro; exact Hf.2.1
        isplitr
        · ipureintro; exact Hf.2.2.1
        ipureintro; exact Hf.2.2.2
      · unfold waitcClose
        icases Hwc with ⟨%γch, Hwc⟩
        wp_apply wp_broadcast_chan_close $$ [$Hwc] as -
        · unfold waitQ; imodintro; itrivial
        (try wp_auto)
        wp_for_post
        iapply HΦ
        iframe
        iright
        isplitr
        · ipureintro; rfl
        unfold putCommitted
        iexists hm.revision, s, hdr, hm
        iframe
        iframe #
        isplitr
        · ipureintro; exact ⟨Hprn, rfl⟩
        isplitr
        · ipureintro; exact Hf.1
        isplitr
        · ipureintro; exact Hf.2.1
        isplitr
        · ipureintro; exact Hf.2.2.1
        ipureintro; exact Hf.2.2.2
  · unfold notCommitted
    (try wp_auto)
    icases Hwc with (%Hwn | Hwc)
    · subst Hwn
      (try wp_auto)
      wp_for_post
      iframe
      iexists _
      simp only [named]
      iframe
    · wp_if_destruct
      · (try wp_auto)
        wp_for_post
        iframe
        iexists _
        simp only [named]
        iframe
      · unfold waitcClose
        icases Hwc with ⟨%γch, Hwc⟩
        wp_apply wp_broadcast_chan_close $$ [$Hwc] as -
        · unfold waitQ; imodintro; itrivial
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
