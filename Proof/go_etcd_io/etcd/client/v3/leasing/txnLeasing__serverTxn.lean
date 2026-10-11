/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/txnLeasing__serverTxn.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.txnLeasing__serverTxn
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__waitSession
public import Spec.go_etcd_io.etcd.client.v3.leasing.gatherOps
public import Spec.go_etcd_io.etcd.client.v3.OpTxn
public import Spec.go_etcd_io.etcd.client.v3.leasing.txnLeasing__fallback
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__LockWriteOps
public import Spec.go_etcd_io.etcd.client.v3.leasing.closeAll
public import Spec.go_etcd_io.etcd.client.v3.leasing.txnLeasing__guard
public import Spec.go_etcd_io.etcd.client.v3.Cmp__KeyBytes
public import Perennial.Proof.strings
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__Evict
public import Spec.go_etcd_io.etcd.client.v3.leasing.txnLeasing__commitToCache
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.ResponseOp__GetResponseTxn
public import Spec.go_etcd_io.etcd.client.v3.leasing.txnLeasing__revokeFallback
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem txnLeasing.serverTxn.wp_proof
    (hws : leasingKV.waitSession.spec (GF := GF) (hG := hG))
    (hgather : gatherOps.spec (GF := GF) (hG := hG))
    (hOpTxn : EtcdGrove.OpTxn.spec (GF := GF) (hG := hG))
    (hfb : txnLeasing.fallback.spec (GF := GF) (hG := hG))
    (hlwo : leaseCache.LockWriteOps.spec (GF := GF) (hG := hG))
    (hclose : closeAll.spec (GF := GF) (hG := hG))
    (hguard : txnLeasing.guard.spec (GF := GF) (hG := hG))
    (hCKey : EtcdGrove.Cmp.KeyBytes.spec (GF := GF) (hG := hG))
    (hevict : leaseCache.Evict.spec (GF := GF) (hG := hG))
    (hctc : txnLeasing.commitToCache.spec (GF := GF) (hG := hG))
    (hGRT : EtcdGrove.ResponseOp.GetResponseTxn.spec (GF := GF) (hG := hG))
    (hrfb : txnLeasing.revokeFallback.spec (GF := GF) (hG := hG)) :
    txnLeasing.serverTxn.spec (GF := GF) (hG := hG) := by
  intro txn lkv γ pfx ctx cs b lo
  wp_start as ⟨Htxn, Hrd, #Hcc, #Hlo⟩
  unfold ownTxnLeasing
  icases Htxn with ⟨%t0, %B0, %csl, %tsl, %esl, %tops, %eops, -, -, -, Hl, #Hlkv, Hc, #Hctx,
    Hcs, Hcso, Hts, Htso, Hes, Heso, %Hops⟩
  obtain ⟨Ht, He⟩ := Hops
  unfold cmpsOwn opsOwn
  icases Hcso with ⟨%cvs, #Hcv, -, %Hcl, #Hcall⟩
  icases Htso with ⟨%tvs, #Htv, Htcap, %Htl, #Htall⟩
  icases Heso with ⟨%evs, #Hev, -, %Hel, #Heall⟩
  wp_apply wp_with_defer as %defer defer
  wp_apply hws $$ [$Hlkv $Hrd $Hctx] as %err ⟨Hrd, Hw⟩
  unfold sessionReadyQ
  icases Hw with (%Herr | ⟨%Herr, ⟨#Hsr, #Hrdy⟩⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok e =>
      wp_auto
      iapply HΦ
      iframe
      iexists tops, eops
      isplitr
      · ipureintro; exact ⟨Ht, He⟩
      unfold txnCommitResult
      ileft; ipureintro; simp
  subst Herr
  wp_auto
  wp_apply (wp_slice_append_persistent tsl tvs esl evs DFrac.discard) $$ [$Htv $Htcap $Hev] as %us ⟨#Hus, -, -⟩
  have Hmapm : (b.thenOs ++ b.elseOs).mapM txnOpOf = some (tops ++ eops) := by
    unfold LTxnBuild.thenOps at Ht; unfold LTxnBuild.elseOps at He
    rw [List.mapM_append, Ht, He]; rfl
  ihave #Husat := opsAt_app us tvs evs b.thenOs b.elseOs Htl Hel $$ [$Hus $Htall $Heall]
  ihave ⟨%uvs, #Huvs, Hul⟩ := opsAt_gather us (b.thenOs ++ b.elseOs) (tops ++ eops) Hmapm $$ Husat
  wp_apply hgather $$ [$Huvs $Hul] as %uops ⟨Huops, %Huops4⟩
  simp only [leavesL_leaves] at Huops4 ⊢
  unfold opsOwn
  icases Huops with ⟨%uv2, #Huv2, -, %Huv2l, #Huv2all⟩
  ihave #Huopsat : opsAt uops (b.thenOs ++ b.elseOs) $$ []
  · unfold opsAt; iexists uv2; iframe #; ipureintro; exact Huv2l
  ihave #Hcmps : cmpsAt csl b.cmps $$ []
  · iapply cmpsSetAt_cmpsAt_c
    unfold cmpsSetAt; iexists cvs; iframe #; ipureintro; exact Hcl
  ihave #Hthen : opsAt tsl b.thenOs $$ []
  · unfold opsAt; iexists tvs; iframe #; ipureintro; exact Htl
  ihave #Helse : opsAt esl b.elseOs $$ []
  · unfold opsAt; iexists evs; iframe #; ipureintro; exact Hel
  ihave #Hcv3 : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  wp_apply hOpTxn $$ [$Hcv3 $Hcmps] as %uv ⟨#Huv, #Huvc, %Huvs⟩
  ihave #Htree := userTxn_tree uv b.cmps tsl esl b.thenOs b.elseOs tops eops Ht He Huvs $$ [$Huv $Huvc $Hthen $Helse]
  wp_apply hfb $$ [$Hl $Hlkv $Huopsat] as %fb ⟨Hl, %fos, #Hfos, %Hfosget⟩
  ihave #Hcache := isLeasingKV_cache $$ Hlkv
  ihave #Hwaitc := leasingX_waitc (GF := GF) lkv γ
  wp_apply hlwo $$ [$Hcache $Hwaitc $Huopsat] as %wsl ⟨%wcs, Hwsl, Hwcap, Hwcs⟩
  ihave ⟨%kv, #Hkvf, #HTxn, #Hpfxf, %Hpfx⟩ := isLeasingKV_kv $$ Hlkv
  ihave IH : iprop("Hl" ∷ structFieldRef txnLeasing go!"lkv" txn ↦ lkv ∗
      "Hc" ∷ structFieldRef txnLeasing go!"ctx" txn ↦ GoInterface.ok ctx ∗
      "Hrd" ∷ lkvReader lkv γ pfx) $$ [Hl Hc Hrd]
  · simp only [named]; iframe
  wp_for IH
  wp_apply hguard $$ [$Hl $Hc $Hlkv $Hrd $Hsr $Hctx $Hcc $Huopsat] as %cmps %gerr ⟨Hl, Hc, Hrd, Hg⟩
  icases Hg with (%Hgerr | ⟨%Hgerr, %ms, #Hms⟩)
  · cases gerr with
    | nil => exact absurd rfl Hgerr
    | ok e =>
      wp_auto
      wp_for_post
      wp_apply hclose $$ [$Hwsl $Hwcs] as Hwsl
      iapply HΦ
      iframe
      iexists tops, eops
      isplitr
      · ipureintro; exact ⟨Ht, He⟩
      unfold txnCommitResult
      ileft; ipureintro; simp
  · subst Hgerr
    wp_auto
    iunfold isEtcdTxnKVO at HTxn
    wp_apply wp_slice_literal (l := [uv])
    isplitr
    · ipureintro; rfl
    iintro %usl ⟨Husl, -⟩
    ipersist Husl
    wp_auto
    wp_apply HTxn $$ %ctx %cs [$Hctx] as %t ⟨%B, HB, #HBs⟩
    iunfold txnBuilderSpecO at HBs
    icases HBs with ⟨#HIf, #HThen, #HElse, #HCommit⟩
    wp_apply_raw HIf $$ %TxnBuild.empty %cmps %ms [$HB]
    · isplitl
      · iexact Hms
      · ipureintro; simp [TxnBuild.empty]
    inext
    iintro HB
    wp_auto
    have hfosm : fos.map txnOpOf = (fos.map TxnOp.get).map some := by
      rw [List.map_map]; exact List.map_congr_left (fun o ho => Hfosget o ho)
    wp_apply_raw HThen $$ %_ %_
      %([OpT.txn OpFull.txnInit b.cmps (b.thenOs.map OpT.leaf) (b.elseOs.map OpT.leaf)] : List OpT)
      %([TxnOp.txn b.cmps tops eops] : List TxnOp) [$HB]
    · isplitl
      · unfold opsTAt
        iexists [uv]
        iframe Husl
        simp only [opListAtC]
        iframe Htree
      · ipureintro
        refine ⟨userTxn_txnOps b.cmps b.thenOs b.elseOs tops eops Ht He, ?_, ?_⟩ <;> rfl
    inext
    iintro HB
    wp_auto
    ihave #Hfb := opsAt_leaves fb fos (fos.map TxnOp.get) hfosm $$ Hfos
    wp_apply_raw HElse $$ %_ %fb %(fos.map OpT.leaf) %(fos.map TxnOp.get) [$HB]
    · isplitl
      · iexact Hfb
      · ipureintro
        exact ⟨txnOps_leaves fos _ hfosm, rfl⟩
    inext
    iintro HB
    wp_auto
    wp_apply_raw HCommit $$ %_ %lo [$HB $Hlo]
    · ipureintro; exact TxnModel.under_nil _
    inext
    iintro %resp %cerr Hcr
    simp only [TxnBuild.empty, TxnModel.empty, List.nil_append]
    unfold txnCommitResultO
    icases Hcr with (⟨%Hcerr, -⟩ | ⟨%Hcerr, Hok⟩)
    · cases cerr with
      | nil => exact absurd rfl Hcerr
      | ok e =>
        wp_auto
        iunfold cmpsAt at Hms
        icases Hms with ⟨%ccs, #Hccs, %Hccl, #Hccall⟩
        ihave %Hccslen := ownSlice_len _ _ _ $$ Hccs
        ihave #Hpeek := leasingX_peek (GF := GF) lkv γ
        ihave #Hstrings : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
        · iPkgInit
        ihave IH2 : iprop(∃ n : w64, "i" ∷ i_ptr ↦ n ∗
            "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ccs.length : Int)⌝) $$ [i]
        · iexists W64 0
          simp only [named]
          iframe
          ipureintro; constructor <;> word
        wp_for IH2
        wp_if_destruct
        · have Hlt : sint.nat n < ccs.length := by word
          obtain ⟨c, Hci⟩ : ∃ c, ccs[sint.nat n]? = some c := ⟨_, List.getElem?_eq_getElem Hlt⟩
          obtain ⟨m, Hmi⟩ : ∃ m, ms[sint.nat n]? = some m :=
            ⟨_, List.getElem?_eq_getElem (by rw [← Hccl]; exact Hlt)⟩
          have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z cmps.len := ⟨Hn.1, by word⟩
          simp only [Hbnd, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index cmps (sint.Z n) ccs DFrac.discard c Hn.1 $$ [Hccs] as -
          · iframe #; ipureintro; exact Hci
          ihave #Hc1 := Hccall $$ %(sint.nat n) %c %m %Hci %Hmi
          iunfold cmpAt at Hc1
          icases Hc1 with ⟨%Hcnn, #Hc2⟩
          iunfold compareAt at Hc2
          icases Hc2 with ⟨%ksl, %esl2, %u, #Hr1, #Hr2, #Hr3, #Hr4, #Hr5, #Hr6, #Hr7, #Hr8⟩
          wp_apply hCKey $$ [$cmp $Hr3] as cmp
          · ipureintro; exact Hcnn
          wp_apply wp_bytes_to_string ksl m.key DFrac.discard $$ [$Hr4] as -
          wp_apply strings.wp_TrimPrefix $$ [$Hstrings]
          wp_apply (hevict (lkvLeases lkv) γ.lc pfx (leasingX lkv γ) (leasingSeen γ)
              (strings.trimPrefix m.key pfx) (fun _ => iprop(True))) $$ [$Hcache $Hpeek] as %rv -
          · iintro %st %tt HX
            imod leasingX_step lkv γ st (st.evict (strings.trimPrefix m.key pfx) tt) $$ HX with ⟨HX, -⟩
            iframe
          wp_for_post
          iframe
          iexists n + W64 1
          simp only [named]
          iframe
          ipureintro; constructor <;> word
        · wp_for_post
          wp_apply hclose $$ [$Hwsl $Hwcs] as Hwsl
          iapply HΦ
          iframe
          iexists tops, eops
          isplitr
          · ipureintro; exact ⟨Ht, He⟩
          unfold txnCommitResult
          ileft; ipureintro; simp
    · subst Hcerr
      iunfold txnCommitOk at Hok
      icases Hok with ⟨%r, %s, %hm, %Hhm, Hresp, #Hreach, %Hfacts, #Hst⟩
      iunfold txnRespOwn at Hresp
      icases Hresp with ⟨%hdr, %rsl, %ps, #Hhdr, #Hhm, Hsucc, #Hrsl, #Hps, Hops⟩
      generalize hok : (runTxn r s ({ cmps := ms, thenOps := [TxnOp.txn b.cmps tops eops], elseOps := List.map TxnOp.get fos } : TxnModel)).1 = ok
      cases ok with
      | true =>
        have ho := runTxn_outer r s (b.model tops eops) ms (fos.map TxnOp.get) hok
        simp only [LTxnBuild.model] at ho
        obtain ⟨ho1, ho2, ho3⟩ := ho
        rw [ho3, ho2, ho1]
        simp only [TxnModel.branch, ↓reduceIte]
        rcases ps with _ | ⟨p0, ps⟩
        · simp only [txnOpsRespOwn]; iexfalso; iexact Hops
        rcases ps with _ | ⟨p1, ps⟩
        rotate_left
        · simp only [txnOpsRespOwn]; iexfalso; icases Hops with ⟨-, H⟩; iexact H
        simp only [txnOpsRespOwn]
        icases Hops with ⟨Hop0, -⟩
        iunfold txnOpRespOwn at Hop0
        icases Hop0 with ⟨%Hp0nn, %w, %tr, %h0, %tsl2, %tps, #Hu, #Hw, %Htrnn, Hth, #Hts2, #Htrsl,
          #Htps, Hbr⟩
        have hmodel : b.model tops eops = { cmps := b.cmps, thenOps := tops, elseOps := eops } := rfl
        have hlin : ({ cmps := ms, thenOps := [TxnOp.txn b.cmps tops eops], elseOps := List.map TxnOp.get fos } : TxnModel).linearizable = true := by
          simp [TxnModel.linearizable, TxnOp.linearizable]
        obtain ⟨Hlo', Hr0, Hr1, Hwf⟩ := Hfacts
        have Htn : ∀ op ∈ tops, ∀ cs ts es, op ≠ .txn cs ts es :=
          mapM_txnOpOf_not_txn b.thenOs tops Ht
        have Hen : ∀ op ∈ eops, ∀ cs ts es, op ≠ .txn cs ts es :=
          mapM_txnOpOf_not_txn b.elseOs eops He
        ihave #Hpbi : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
        · iPkgInit
        cases hok2 : (runTxn r s { cmps := b.cmps, thenOps := tops, elseOps := eops }).1
        all_goals
          simp only [Bool.false_eq_true, ↓reduceIte]
          icases Hbr with #Hbr
          ihave #Hn : txnOpRespN p0 (TxnOp.txn b.cmps tops eops)
              (TxnOpResult.txn (runTxn r s { cmps := b.cmps, thenOps := tops, elseOps := eops }).1
                (runTxn r s { cmps := b.cmps, thenOps := tops, elseOps := eops }).2.2) $$ []
          · rw [hok2]
            simp only [txnOpRespN]
            isplitr
            · ipureintro; exact Hp0nn
            iexists w, tr, tsl2, tps
            iframe #
            ipureintro; exact Htrnn
          wp_auto
          wp_apply hctc $$ [$Hl $Hlkv $Hhdr $Hhm $Hrsl $Hps $Hn $Htree] as Hl
          · ipureintro
            have h := userTxn_txnOps b.cmps b.thenOs b.elseOs tops eops Ht He
            simp only [OpT.txnOps] at h
            revert h; split <;> simp_all
          ihave %Hrsllen := ownSlice_len _ _ _ $$ Hps
          have h0 : sint.Z (W64 0) = 0 := by decide
          rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z rsl.len by
            rw [h0]; have := Hrsllen.1; simp at this; word))]
          wp_apply wp_load_slice_index rsl (sint.Z (W64 0)) [p0] _ p0 (by decide) $$ [Hps] as -
          · iframe Hps; ipureintro; rfl
          wp_apply hGRT p0 w tr $$ [$Hpbi $Hu $Hw]
          · ipureintro; exact Hp0nn
          wp_for_post
          ipersist Hth
          wp_apply hclose $$ [$Hwsl $Hwcs] as Hwsl
          iapply HΦ
          iframe Hrd
          iexists tops, eops
          isplitr
          · ipureintro; exact ⟨Ht, He⟩
          unfold txnCommitResult
          iright
          isplitr
          · ipureintro; rfl
          iexists r, s
          rw [hmodel, hok2]
          simp only [TxnModel.branch, Bool.false_eq_true, ↓reduceIte]
          iframe Hreach Hst
          isplitr
          · unfold txnRespAt
            ihave ⟨%Hlen, #Hall⟩ := txnOpsRespN_flat _ _ _ (by assumption) $$ Hbr
            iunfold hdrFull at Hhm
            icases Hhm with ⟨%Hhnn, -, -, #Hrev, -, -⟩
            ihave #Hrev' : structFieldRef etcdserverpb.ResponseHeader go!"Revision" hdr ↦□ r $$ []
            · rw [← Hhm]; iexact Hrev
            iexists hdr, tsl2, tps
            iframe #
            ipureintro; exact ⟨Hhnn, Hlen⟩
          ipureintro
          exact ⟨fun _ => Hlo' hlin, Hr0, Hr1, Hwf⟩

      | false =>
        simp only [TxnModel.branch, Bool.false_eq_true, ↓reduceIte]
        imod fallbackResps_ro $$ Hops with ⟨%kvss, %Hkl, Hro⟩
        wp_auto
        wp_apply hrfb $$ [$Hl $Hc $Hlkv $Hrd $Hsr $Hctx $Hcc $Hps $Hro] as %ferr ⟨Hl, Hc, Hrd⟩
        · ipureintro; exact Hkl
        cases ferr with
        | ok e =>
          wp_auto
          wp_for_post
          wp_apply hclose $$ [$Hwsl $Hwcs] as Hwsl
          iapply HΦ
          iframe
          iexists tops, eops
          isplitr
          · ipureintro; exact ⟨Ht, He⟩
          unfold txnCommitResult
          ileft; ipureintro; simp
        | nil =>
          wp_auto
          wp_for_post
          iframe
          simp only [named]
          iframe

end proof

end leasing
end EtcdGrove
end Perennial
