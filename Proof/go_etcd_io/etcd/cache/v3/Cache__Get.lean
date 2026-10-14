/-
Proof of `Spec/Cache__Get.lean`: the end-to-end `Get` theorem. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Cache__Get
public import Spec.go_etcd_io.etcd.cache.v3.store__LatestRev
public import Spec.go_etcd_io.etcd.cache.v3.Cache__WaitReady
public import Spec.go_etcd_io.etcd.client.v3.OpGet
public import Spec.go_etcd_io.etcd.cache.v3.Cache__validateGet
public import Spec.go_etcd_io.etcd.client.v3.Op__RangeBytes
public import Spec.go_etcd_io.etcd.client.v3.Op__Rev
public import Spec.go_etcd_io.etcd.client.v3.Op__IsSerializable
public import Spec.go_etcd_io.etcd.cache.v3.Cache__serverRevision
public import Spec.go_etcd_io.etcd.cache.v3.Cache__waitTillRevision
public import Spec.go_etcd_io.etcd.cache.v3.store__Get

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem Cache.Get.wp_proof
    (wp_LatestRev : store.LatestRev.spec (GF := GF) (hG := hG))
    (wp_WaitReady : Cache.WaitReady.spec (GF := GF) (hG := hG))
    (wp_OpGet : OpGet.spec (GF := GF) (hG := hG))
    (wp_validateGet : Cache.validateGet.spec (GF := GF) (hG := hG))
    (wp_RangeBytes : Op.RangeBytes.spec (GF := GF) (hG := hG))
    (wp_Rev : Op.Rev.spec (GF := GF) (hG := hG))
    (wp_IsSerializable : Op.IsSerializable.spec (GF := GF) (hG := hG))
    (wp_serverRevision : Cache.serverRevision.spec (GF := GF) (hG := hG))
    (wp_waitTillRevision : Cache.waitTillRevision.spec (GF := GF) (hG := hG))
    (wp_store_Get : store.Get.spec (GF := GF) (hG := hG)) :
    Cache.Get.spec (GF := GF) (hG := hG) := by
  intro c cf γr γd cap r0 ctx s key sl gs
  wp_start as ⟨#Hc, #Hctx, #Hopts, %Hnp, Hrd, #Hlb⟩
  ihave #Hcl : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Hc' := Hc
  iunfold isCacheFields at Hc'
  iNamed Hc'
  wp_auto
  unfold cacheReader
  wp_apply wp_LatestRev cf.store cf.γs cf.scap (etcdCert cf.pfx) (cacheRev cf) r0 $$ [$HisStore $Hrd $Hlb]
    as %lr ⟨Hrd, %st0, #Hseen0, #-, %Hlr⟩
  ihave Hci : (cacheInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hci with ⟨⟨%eNR, #HeNR⟩, -, ⟨%eKR, #HeKR⟩, ⟨%eCT, #HeCT⟩, -⟩
  ihave #Hrpc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
  · iPkgInit
  ihave Hri : (rpctypesInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hrpc
  icases Hri with ⟨⟨%eFR, #HeFR⟩, ⟨%eCP, #HeCP, -⟩, -⟩
  iunfold storeSeen at Hseen0
  icases Hseen0 with ⟨%Hst0, #Hlbst0⟩
  imod monoNatLbOwn_0 (GF := GF) γr.epoch with #Hep0
  wp_if_destruct
  focus
    wp_apply wp_WaitReady c cf γr γd cap 0 ctx s $$ [$Hc $Hctx] as %err Herr
    · unfold readyEpochLb; iexact Hep0
    iunfold readyWaitResult at Herr
    icases Herr with (⟨%Hnil, -⟩ | ⟨%Hne, #HPD, #Hcl⟩)
    focus
      subst Hnil
      wp_auto
    rotate_left
    -- not ready, and the context is done
    · obtain ⟨e, rfl⟩ : ∃ e, err = GoInterface.ok e := by
        cases err with
        | nil => exact absurd rfl Hne
        | ok e => exact ⟨e, rfl⟩
      wp_auto
      iapply HΦ
      iframe Hrd
      unfold cacheGetResult cacheGetErr
      ileft
      isplitr
      · ipureintro; rfl
      ileft
      iframe HPD Hcl
      ipureintro; exact Hne
  all_goals
    wp_apply wp_OpGet key sl gs $$ [$Hopts] as %op #HopF
    · ipureintro; exact Hnp
    generalize Ho : (opGetModel key gs) = of at *
    iunfold opFullAt at HopF
    icases HopF with ⟨#HopAt, -, -⟩
    wp_apply wp_validateGet c cf γr γd cap key op of.base $$ [$Hc $HopAt] as %f %verr #Hval
    iunfold validateResult at Hval
    cases hu : of.base.getUnsupported
    focus
      rw [ite_eq_right (by simp)] at *
      cases hv : validRange cf.pfx key of.base.rangeEnd
      · -- the range is outside the prefix: `ErrKeyRangeInvalid`
        rw [ite_eq_right (by simp)] at *
        icases Hval with ⟨%Hf, #HeKR'⟩
        icombine HeKR HeKR' gives %Heq
        subst Heq
        wp_auto
        iapply HΦ
        iframe Hrd
        unfold cacheGetResult cacheGetErr
        ileft
        isplitr
        · ipureintro; rfl
        iright; iright; ileft
        iframe HeKR'
        ipureintro; exact ⟨hu, hv⟩
      rw [ite_eq_left rfl] at *
      icases Hval with ⟨%Hvf, -⟩
      obtain ⟨Hvnil, -⟩ := Hvf
      subst Hvnil
      wp_auto
      wp_apply wp_string_to_bytes key as %ssl ⟨Hssl, -⟩
      wp_apply wp_RangeBytes op_ptr op of.base (DFrac.own 1) $$ [$op $HopAt] as %esl ⟨op, #Hesl⟩
      wp_apply wp_Rev op_ptr op of.base (DFrac.own 1) $$ [$op $HopAt] as op
      wp_apply wp_IsSerializable op_ptr op of.base (DFrac.own 1) $$ [$op $HopAt] as op
      cases hs : of.base.serializable
      focus
        -- linearizable: catch up with etcd's current revision first
        simp only [Bool.not_false]
        wp_auto
        wp_apply wp_serverRevision c cf γr γd cap ctx s $$ [$Hc $Hctx] as %srev %serr Hsr
        icases Hsr with (⟨%Hsn, %m', #Hm'⟩ | %Hsne)
        rotate_left
        · -- the client's error
          obtain ⟨Hne, rfl⟩ := Hsne
          obtain ⟨e, rfl⟩ : ∃ e, serr = GoInterface.ok e := by
            cases serr with
            | nil => exact absurd rfl Hne
            | ok e => exact ⟨e, rfl⟩
          wp_auto
          iapply HΦ
          iframe Hrd
          unfold cacheGetResult cacheGetErr
          ileft
          isplitr
          · ipureintro; rfl
          iright; iright; iright; ileft
          ipureintro; exact ⟨hs, Hne⟩
        subst Hsn
        wp_auto
        wp_if_destruct
        · -- a future revision: `rpctypes.ErrFutureRev`
          iapply HΦ
          iframe Hrd
          unfold cacheGetResult cacheGetErr
          ileft
          isplitr
          · ipureintro; rfl
          iright; iright; iright; iright; ileft
          iframe HeFR
          isplitr
          · ipureintro; exact hs
          iexists srev, m'
          iframe Hm'
          ipureintro; omega
        have Hle : sint.Z of.base.rev ≤ sint.Z srev := by omega
        wp_apply wp_waitTillRevision c cf γr γd cap ctx s srev $$ [$Hc $Hctx Hrd]
          as %werr ⟨Hrd, Hw⟩
        · unfold cacheReader; iexact Hrd
        unfold cacheReader
        unfold waitResult
        icases Hw with (⟨%Hwn, #Hlbs⟩ | #HeCT' | ⟨%Hwne, #HPD, #Hcl⟩)
        focus
          subst Hwn
          wp_auto
          ihave Hfresh : iprop(∃ r0' : w64, storeRevLb cf.γs r0' ∗ ⌜sint.Z r0 ≤ sint.Z r0'⌝ ∗
              (if of.base.serializable then iprop(True)
               else iprop(∃ (serverRev : w64) (m'' : KvMap), isEtcdKvs serverRev cf.pfx m'' ∗
                 ⌜sint.Z of.base.rev ≤ sint.Z serverRev ∧ sint.Z serverRev ≤ sint.Z r0'⌝))) $$ []
          · rw [hs]
            simp only [Bool.false_eq_true, ↓reduceIte]
            by_cases hr : sint.Z r0 ≤ sint.Z srev
            · iexists srev
              iframe Hlbs
              isplitr
              · ipureintro; exact hr
              iexists srev, m'
              iframe Hm'
              ipureintro; omega
            · iexists r0
              iframe Hlb
              isplitr
              · ipureintro; omega
              iexists srev, m'
              iframe Hm'
              ipureintro; omega
        rotate_left
        · -- timed out: `ErrCacheTimeout`
          icombine HeCT HeCT' gives %Heq
          subst Heq
          wp_auto
          iapply HΦ
          iframe Hrd
          unfold cacheGetResult cacheGetErr
          ileft
          isplitr
          · ipureintro; rfl
          iright; iright; iright; iright; iright; ileft
          iframe HeCT'
          ipureintro; exact hs
        · -- the context is done
          obtain ⟨e, rfl⟩ : ∃ e, werr = GoInterface.ok e := by
            cases werr with
            | nil => exact absurd rfl Hwne
            | ok e => exact ⟨e, rfl⟩
          wp_auto
          iapply HΦ
          iframe Hrd
          unfold cacheGetResult cacheGetErr
          ileft
          isplitr
          · ipureintro; rfl
          ileft
          iframe HPD Hcl
          ipureintro; exact Hwne
      rotate_left
      focus
        -- serializable: answer from the cache as it is
        try simp only [Bool.not_true]
        try wp_auto
        ihave Hfresh : iprop(∃ r0' : w64, storeRevLb cf.γs r0' ∗ ⌜sint.Z r0 ≤ sint.Z r0'⌝ ∗
              (if of.base.serializable then iprop(True)
               else iprop(∃ (serverRev : w64) (m'' : KvMap), isEtcdKvs serverRev cf.pfx m'' ∗
                 ⌜sint.Z of.base.rev ≤ sint.Z serverRev ∧ sint.Z serverRev ≤ sint.Z r0'⌝))) $$ []
        · rw [hs]
          try simp only [↓reduceIte]
          iexists r0
          iframe Hlb
          isplitr
          · ipureintro; omega
          itrivial
      all_goals
        icases Hfresh with ⟨%r0', #Hlb', %Hr0', Hfr⟩
        wp_apply wp_store_Get cf.store cf.γs cf.scap (etcdCert cf.pfx) (cacheRev cf) r0' ssl esl key
          of.base.rangeEnd (DFrac.own 1) DFrac.discard of.base.rev $$ [$HisStore $Hrd $Hlb' $Hssl $Hesl]
          as %kvs %lrev %gerr ⟨Hrd, Hssl, -, %st, #Hseen, #-, #Herr, Hres⟩
        iunfold storeSeen at Hseen
        icases Hseen with ⟨%Hst, #Hlbst⟩
        generalize Hm : snapModel st of.base.rev = res
        cases res with
        | ok r m =>
          simp only [snapErr]
          icases Herr with %Hgn
          subst Hgn
          icases Hres with ⟨%Hlrev, #HE, Hkvs, Hcap, #HkvsAt⟩
          wp_auto
          wp_alloc rp as Hrp
          wp_auto
          ihave %Hkl := ownSlice_len _ _ _ $$ Hkvs
          have hcnt : kvs.len = W64 (kvRange key of.base.rangeEnd m).length := by
            simp only [List.length_map] at Hkl
            obtain ⟨h1, h2⟩ := Hkl
            apply BitVec.eq_of_toInt_eq
            word
          subst Hlrev
          iapply HΦ
          iframe Hrd
          unfold cacheGetResult cacheGetOk
          iright
          isplitr
          · ipureintro; rfl
          iexists «$v0_ptr», kvs, st, r, m
          isplitl [Hrp]
          · unfold getRespVal; rw [← hcnt]; iexact Hrp
          isplitl [«$v0»]
          · unfold respHeaderVal; iexact «$v0»
          iframe Hkvs Hcap HkvsAt
          isplitr
          · iunfold etcdCert at HE; iexact HE
          isplitr
          · unfold storeSeen; iframe Hlbst; ipureintro; exact ⟨Hst.1, by omega⟩
          isplitr
          · ipureintro; exact ⟨Hm, hu, hv⟩
          cases hs' : of.base.serializable
          · rw [hs'] at *
            simp only [Bool.false_eq_true, ↓reduceIte] at *
            icases Hfr with ⟨%sr, %m'', #Hsr, %Hsrle⟩
            iexists sr, m''
            iframe Hsr
            ipureintro; omega
          · simp only [↓reduceIte]; itrivial
        | notReady =>
          simp only [snapErr]
          icombine Herr HeNR gives %Heq
          subst Heq
          icases Hres with %Hres
          obtain ⟨-, -⟩ := Hres
          wp_auto
          iapply HΦ
          iframe Hrd
          unfold cacheGetResult cacheGetErr
          ileft
          isplitr
          · ipureintro; rfl
          iright; iright; iright; iright; iright; iright
          iexists st
          rw [Hm]
          unfold storeSeen
          iframe Hlbst
          simp only [snapErr]
          iframe HeNR
          ipureintro
          exact ⟨⟨Hst.1, by omega⟩, by intro r m h; cases h⟩
        | invalid =>
          simp only [snapErr]
          icases Herr with %Hge
          obtain ⟨e, rfl⟩ := Hge
          icases Hres with %Hres
          obtain ⟨-, -⟩ := Hres
          wp_auto
          iapply HΦ
          iframe Hrd
          unfold cacheGetResult cacheGetErr
          ileft
          isplitr
          · ipureintro; rfl
          iright; iright; iright; iright; iright; iright
          iexists st
          rw [Hm]
          unfold storeSeen
          iframe Hlbst
          simp only [snapErr]
          ipureintro
          exact ⟨⟨Hst.1, by omega⟩, ⟨e, rfl⟩, by intro r m h; cases h⟩
        | future =>
          simp only [snapErr]
          icombine Herr HeFR gives %Heq
          subst Heq
          icases Hres with %Hres
          obtain ⟨-, -⟩ := Hres
          wp_auto
          iapply HΦ
          iframe Hrd
          unfold cacheGetResult cacheGetErr
          ileft
          isplitr
          · ipureintro; rfl
          iright; iright; iright; iright; iright; iright
          iexists st
          rw [Hm]
          unfold storeSeen
          iframe Hlbst
          simp only [snapErr]
          iframe HeFR
          ipureintro
          exact ⟨⟨Hst.1, by omega⟩, by intro r m h; cases h⟩
        | compacted =>
          simp only [snapErr]
          icombine Herr HeCP gives %Heq
          subst Heq
          icases Hres with %Hres
          obtain ⟨-, -⟩ := Hres
          wp_auto
          iapply HΦ
          iframe Hrd
          unfold cacheGetResult cacheGetErr
          ileft
          isplitr
          · ipureintro; rfl
          iright; iright; iright; iright; iright; iright
          iexists st
          rw [Hm]
          unfold storeSeen
          iframe Hlbst
          simp only [snapErr]
          iframe HeCP
          ipureintro
          exact ⟨⟨Hst.1, by omega⟩, by intro r m h; cases h⟩
    · -- an unsupported option
      rw [ite_eq_left rfl] at *
      icases Hval with ⟨-, %e, %He, -⟩
      subst He
      wp_auto
      iapply HΦ
      iframe Hrd
      unfold cacheGetResult cacheGetErr
      ileft
      isplitr
      · ipureintro; rfl
      iright; ileft
      ipureintro; exact ⟨hu, by intro h; cases h⟩

end proof

end EtcdGrove
end Perennial
