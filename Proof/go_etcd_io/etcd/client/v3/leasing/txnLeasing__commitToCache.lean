/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/txnLeasing__commitToCache.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.txnLeasing__commitToCache
public import Spec.go_etcd_io.etcd.client.v3.leasing.gatherResponseOps
public import Spec.go_etcd_io.etcd.client.v3.Op__KeyBytes
public import Spec.go_etcd_io.etcd.client.v3.Op__IsDelete
public import Spec.go_etcd_io.etcd.client.v3.Op__RangeBytes
public import Spec.go_etcd_io.etcd.client.v3.leasing.inRange
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__delete
public import Spec.go_etcd_io.etcd.client.v3.Op__IsPut
public import Spec.go_etcd_io.etcd.client.v3.Op__ValueBytes
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__Update
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingCommitLemmas

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

theorem txnLeasing.commitToCache.wp_proof
    (hgro : gatherResponseOps.spec (GF := GF) (hG := hG))
    (hKey : EtcdGrove.Op.KeyBytes.spec (GF := GF) (hG := hG))
    (hIsDel : EtcdGrove.Op.IsDelete.spec (GF := GF) (hG := hG))
    (hRange : EtcdGrove.Op.RangeBytes.spec (GF := GF) (hG := hG))
    (hinRange : inRange.spec (GF := GF) (hG := hG))
    (hdel : leaseCache.delete.spec (GF := GF) (hG := hG))
    (hIsPut : EtcdGrove.Op.IsPut.spec (GF := GF) (hG := hG))
    (hVal : EtcdGrove.Op.ValueBytes.spec (GF := GF) (hG := hG))
    (hupd : leaseCache.Update.spec (GF := GF) (hG := hG)) :
    txnLeasing.commitToCache.spec (GF := GF) (hG := hG) := by
  intro txn lkv γ pfx dq resp hdr hm rsl p0 top res uv t
  wp_start as ⟨Hl, #Hlkv, #Hhdr, #Hhm, #Hrsl, #Hps, #Hp0, #Huv, %Htop⟩
  wp_auto
  wp_apply wp_slice_literal (l := [uv])
  isplitr
  · ipureintro; rfl
  iintro %usl ⟨Husl, -⟩
  ipersist Husl
  wp_apply hgro rsl [p0] _ [uv] [t] [top] [res] $$ [$Hps $Husl] as %ops Hops
  · isplitr
    · simp only [txnOpsRespN]; iframe #
    isplitr
    · simp only [opListAtC]; iframe #
    ipureintro; simp [OpT.txnOps, Htop]
  unfold opsOwn
  icases Hops with ⟨%ovs, #Hovs, -, %Hovl, #Hovall⟩
  ihave %Hovlen := ownSlice_len _ _ _ $$ Hovs
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hcache := isLeasingKV_cache $$ Hlkv
  simp only [lkvCache, isLeaseCache]
  icases Hcache with ⟨#Hguard, -⟩
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hguard] as ⟨Hwl, HP⟩
  icases leaseCacheInv_open_w $$ HP with ⟨%st0, Hown, HX, Hinst, Hready, #Hfacts, %Hwf, Hclose⟩
  ihave IH : iprop(∃ (n : w64) (opv : go_etcd_io.etcd.client.v3.Op) (st : LeaseCacheSt),
      "i" ∷ i_ptr ↦ n ∗ "op" ∷ op_ptr ↦ opv ∗ "Hown" ∷ lcOwn (lkvLeases lkv) st (DFrac.own 1) ∗
      "%Hsame" ∷ ⌜CacheSame st0 st⌝ ∗ "#Hf" ∷ □ lcFacts pfx st ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ovs.length : Int)⌝) $$ [i op Hown]
  · iexists W64 0, _, st0
    simp only [named]
    iframe
    iframe #
    ipureintro; exact ⟨cacheSame_refl st0 Hwf, by word, by word⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < ovs.length := by word
    obtain ⟨v, Hvi⟩ : ∃ v, ovs[sint.nat n]? = some v := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨o, Hoi⟩ : ∃ o, (OpT.chosenL [t] [res])[sint.nat n]? = some o :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hovl]; exact Hlt)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z ops.len := ⟨Hn.1, by word⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index ops (sint.Z n) ovs DFrac.discard v Hn.1 $$ [Hovs] as -
    · iframe #; ipureintro; exact Hvi
    ihave #Hat := Hovall $$ %(sint.nat n) %v %o %Hvi %Hoi
    wp_apply hKey $$ [$op $Hat] as %ksl ⟨op, #Hk⟩
    wp_apply wp_bytes_to_string ksl o.key DFrac.discard $$ [$Hk] as -
    wp_apply hIsDel $$ [$op $Hat] as op
    ihave #Hat' := Hat
    iunfold opFullAt at Hat'
    icases Hat' with ⟨#Hbase, -⟩
    by_cases h3 : o.t = W64 3
    · rw [decide_eq_true h3]
      wp_apply hRange $$ [$op $Hbase] as %esl ⟨op, #He⟩
      ihave %Helen := ownSlice_len _ _ _ $$ He
      by_cases hr : o.base.rangeEnd = []
      · have hlen0 : sint.Z esl.len = 0 := by
          have := Helen.1; rw [hr] at this; simp at this; word
        rw [decide_eq_false (by word : ¬ sint.Z (W64 0) < sint.Z esl.len)]
        wp_auto
        wp_apply hIsDel $$ [$op $Hat] as op
        rw [decide_eq_true h3]
        wp_auto
        wp_apply hdel $$ [$Hown $Hhm] as ⟨%h', Hown⟩
        · ipureintro; exact Hsame.1
        have Hsame' := cacheSame_modify st0 st o.key (fun e => e.del h' hm)
          (fun e => (del_fields e h' hm).1) Hsame
        ihave #Hf' := modify_facts pfx o.key (fun e => e.del h' hm) st
          (fun e => (del_fields e h' hm).2) $$ Hf
        wp_apply hIsPut $$ [$op $Hat] as op
        rw [decide_eq_false (by rw [h3]; decide : ¬ (o.t = W64 2))]
        wp_auto
        wp_for_post
        iframe
        iexists (n + W64 1), v, (st.modify o.key (fun e => e.del h' hm))
        simp only [named]
        iframe
        iframe #
        ipureintro; exact ⟨Hsame', by word, by word⟩
      · have hlenpos : sint.Z (W64 0) < sint.Z esl.len := by
          have h1 := Helen.1
          have : o.base.rangeEnd.length ≠ 0 := by simpa using hr
          have e1 : ((sint.nat esl.len : Nat) : Int) = sint.Z esl.len := Int.toNat_of_nonneg Helen.2
          have : (0 : Int) < sint.Z esl.len := by omega
          word
        rw [decide_eq_true hlenpos]
        wp_auto
        wp_apply hRange $$ [$op $Hbase] as %esl2 ⟨op, #He2⟩
        wp_apply wp_bytes_to_string esl2 o.base.rangeEnd DFrac.discard $$ [$He2] as -
        icases lcOwn_emap_acc $$ Hown with ⟨Hentries, Hemap, Hcl⟩
        wp_auto
        by_cases hnil : st.emap = map.nil
        · rw [hnil]
          wp_func_lits
          wp_auto
          ihave Hown := Hcl $$ Hentries Hemap
          have HSAME := Hsame
          wp_apply hIsPut $$ [$op $Hat] as op
          rw [decide_eq_false (by rw [h3]; decide : ¬ (o.t = W64 2))]
          wp_auto
          wp_for_post
          iframe
          iexists (n + W64 1), v, st
          simp only [named]
          iframe
          iframe #
          ipureintro; exact ⟨HSAME, by word, by word⟩
        · ihave Hemap : st.emap ↦$ st.lis $$ [Hemap]
          · simp only [emapOwn, hnil, ↓reduceIte]; iexact Hemap
          wp_func_lits
          wp_bind (App (App (Val (map.forRange _ _)) _) _)
          iapply wp_map_for_range_gen (fun (keys : List GoString) (i : Nat) (m' : GMap GoString Loc) =>
              iprop(∃ (stc : LeaseCacheSt) (kv : GoString),
              "Hentries" ∷ structFieldRef leaseCache go!"entries" (lkvLeases lkv) ↦ st.emap ∗
              "Hcl" ∷ (structFieldRef leaseCache go!"entries" (lkvLeases lkv) ↦ stc.emap -∗
                  emapOwn stc (DFrac.own 1) -∗ lcOwn (lkvLeases lkv) stc (DFrac.own 1)) ∗
              "%Hs" ∷ ⌜CacheSame st0 stc ∧ m' = st.lis ∧ stc.lis = st.lis ∧ stc.emap = st.emap⌝ ∗
              "#Hfc" ∷ □ lcFacts pfx stc ∗
              "k" ∷ k_ptr ↦ kv ∗ "key" ∷ key_ptr ↦ o.key ∗ "Hend" ∷ end_ptr ↦ o.base.rangeEnd ∗
              "txn" ∷ txn_ptr ↦ txn ∗ "Hl" ∷ structFieldRef txnLeasing go!"lkv" txn ↦{dq} lkv ∗
              "txnResp" ∷ txnResp_ptr ↦ resp))
            _ _ _ st.emap st.lis (DFrac.own 1) $$ Hemap
          iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
          isplitl [Hentries Hcl k key «end» txn Hl txnResp]
          · iexists st, _
            simp only [named]
            iframe Hcl
            iframe
            iframe #
            ipureintro; exact ⟨Hsame, trivial, trivial, trivial⟩
          isplitr
          · imodintro
            iintro %i %kk %vv %m' ⟨%Hki, %Hmv⟩ HP Hm
            iNamed HP
            obtain ⟨hs1, rfl, hs3, hs4⟩ := Hs
            wp_auto
            wp_apply hinRange
            cases hrg : leaseInRange kk o.key o.base.rangeEnd
            · wp_auto
              unfold forMapPostcondition
              iright; ileft
              isplitr
              · ipureintro; rfl
              iexists st.lis
              iframe Hm
              iexists stc, kk
              simp only [named]
              iframe
              iframe #
              ipureintro; refine ⟨hs1, ?_, ?_, ?_⟩ <;> simp_all
            · wp_auto
              ihave Hown := Hcl $$ [Hentries] [Hm]
              · rw [hs4]; iexact Hentries
              · simp only [emapOwn, hs4, hnil, ↓reduceIte, hs3]; iexact Hm
              wp_apply hdel $$ [$Hown $Hhm] as ⟨%h', Hown⟩
              · ipureintro; exact hs1.1
              have hs1' := cacheSame_modify st0 stc kk (fun e => e.del h' hm)
                (fun e => (del_fields e h' hm).1) hs1
              ihave #Hfc' := modify_facts pfx kk (fun e => e.del h' hm) stc
                (fun e => (del_fields e h' hm).2) $$ Hfc
              icases lcOwn_emap_acc $$ Hown with ⟨Hentries, Hemap, Hcl⟩
              have hmo := modify_other kk (fun e => e.del h' hm) stc
              have hml := modify_lis kk (fun e => e.del h' hm) stc (fun e => (del_fields e h' hm).1)
              unfold forMapPostcondition
              iright; ileft
              isplitr
              · ipureintro; rfl
              iexists st.lis
              isplitl [Hemap]
              · simp only [emapOwn, hmo.1, hs4, hnil, ↓reduceIte, hml, hs3]; iexact Hemap
              iexists (stc.modify kk (fun e => e.del h' hm)), kk
              simp only [named]
              isplitl [Hentries]
              · rw [hmo.1, hs4]; iexact Hentries
              iframe
              iframe #
              ipureintro; refine ⟨hs1', ?_, ?_, ?_⟩ <;> simp_all
          isplitr
          · imodintro
            iintro %i %kk %m' ⟨%Hki, %Hnone⟩ HP
            iNamed HP
            obtain ⟨hs1, rfl, hs3, hs4⟩ := Hs
            exfalso
            have := (Hkset kk).1 (List.mem_of_getElem? Hki)
            rw [Hnone] at this; simp at this
          iintro %m' HP Hm
          iNamed HP
          obtain ⟨hs1, rfl, hs3, hs4⟩ := Hs
          ihave Hown := Hcl $$ [Hentries] [Hm]
          · rw [hs4]; iexact Hentries
          · simp only [emapOwn, hs4, hnil, ↓reduceIte, hs3]; iexact Hm
          wp_auto
          have HSAME := hs1
          wp_apply hIsPut $$ [$op $Hat] as op
          rw [decide_eq_false (by rw [h3]; decide : ¬ (o.t = W64 2))]
          wp_auto
          wp_for_post
          iframe
          iexists (n + W64 1), v, stc
          simp only [named]
          iframe
          iframe #
          ipureintro; exact ⟨HSAME, by word, by word⟩
    · rw [decide_eq_false h3]
      wp_auto
      wp_apply hIsDel $$ [$op $Hat] as op
      rw [decide_eq_false h3]
      wp_auto
      wp_apply hIsPut $$ [$op $Hat] as op
      by_cases h2 : o.t = W64 2
      · rw [decide_eq_true h2]
        wp_auto
        wp_apply hKey $$ [$op $Hat] as %ksl2 ⟨op, #Hk2⟩
        wp_apply hVal $$ [$op $Hat] as %vsl ⟨op, #Hv⟩
        wp_apply (hupd (lkvLeases lkv) st ksl2 o.key vsl o.val hdr hm) $$ [$Hown $Hk2 $Hv $Hhm] as ⟨%p, %sl', Hown⟩
        · ipureintro; exact Hsame.1
        have Hsame' := cacheSame_modify st0 st o.key
          (fun e => e.update (freshKv p ksl2 o.key hm.revision) sl' hdr hm vsl o.val)
          (fun e => (update_fields e _ sl' hdr hm vsl o.val).1) Hsame
        ihave #Hf' := modify_facts pfx o.key
          (fun e => e.update (freshKv p ksl2 o.key hm.revision) sl' hdr hm vsl o.val) st
          (fun e => ⟨(update_fields e _ sl' hdr hm vsl o.val).2.1,
            (update_fields e _ sl' hdr hm vsl o.val).2.2.2.2.2.1,
            (update_fields e _ sl' hdr hm vsl o.val).2.2.2.2.2.2⟩) $$ Hf
        wp_for_post
        iframe
        iexists (n + W64 1), v, (st.modify o.key (fun e => e.update (freshKv p ksl2 o.key hm.revision) sl' hdr hm vsl o.val))
        simp only [named]
        iframe
        iframe #
        ipureintro; exact ⟨Hsame', by word, by word⟩
      · rw [decide_eq_false h2]
        wp_auto
        have Hsame' := Hsame
        wp_for_post
        iframe
        iexists (n + W64 1), v, st
        simp only [named]
        iframe
        iframe #
        ipureintro; exact ⟨Hsame', by word, by word⟩
  · obtain ⟨hwf, hi, hr, -, -⟩ := Hsame
    imod leasingX_step lkv γ st0 st $$ HX with ⟨HX, -⟩
    ihave Hinst : monoListAuthOwn γ.lc.inst 1 st.installed $$ [Hinst]
    · rw [hi]; iexact Hinst
    ihave Hready : monoNatAuthOwn γ.lc.ready 1 st.readyN $$ [Hready]
    · rw [hr]; iexact Hready
    imod Hclose $$ %st %hwf Hf Hinst Hready Hown HX with HP
    wp_apply sync.RWMutex.wp_Unlock_guard $$ [$Hwl $HP]
    iapply HΦ
    iframe

end proof

end leasing
end EtcdGrove
end Perennial
