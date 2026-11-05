/-
**The snapshot image's laws of mvcc's API** (stage 2, M2, 2026-11-05: `notes/mvcc-api-risk.md`,
M2), over the sealed definitions (`Api.lean`: `mvccImage`, its pure part `snap.imageOk`,
`Api/SnapImage.lean`). Lean-first (no Rocq counterpart).
- `mvccImage_persistent` (the image's conjunct of `persistent.law`);
- `mvccImage_fresh.law_holds`: a fresh backend's data is the empty history's image, its receipt
  `⧖ 0` allocated (`preceipt_zero`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.SnapImage
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.SnapFreeze
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

instance mvccImage_persistent (D : backend.Data) (L : Log) (c : Int) (u : Bool) :
    Persistent (mvccImage (GF := GF) D L c u) := by
  unfold mvccImage; infer_instance

/-- **`mvccImage_fresh.law`**: no change, so the receipt `⧖ 0`; the facts `snap.imageOk_fresh`. -/
theorem mvccImage_fresh.law_holds : mvccImage_fresh.law (GF := GF) := by
  intro D hk hs hf
  iintro
  imod preceipt_zero (GF := GF) with #H0
  imodintro
  unfold mvccImage
  isplitl
  · rw [show logCh mvccStart.log = 0 from rfl]
    iexact H0
  · ipureintro; exact snap.imageOk_fresh D hk hs hf

instance isMvcc_persistent (kv : GoInterface) (γ : MvccName) :
    Persistent (isMvcc (GF := GF) kv γ) := by
  unfold isMvcc; infer_instance

/-- **A store's handle is a store's** (a plain store, or the watchable store's inner one). -/
private theorem isMvcc_store (kv : GoInterface) (γ : MvccName) :
    isMvcc (GF := GF) kv γ ⊢ ∃ s : Loc, isStore s (γ : StoreNames) := by
  iintro Hmv
  iunfold isMvcc at Hmv
  icases Hmv with #(Hmv | Hmv)
  · iunfold isMvccPlain at Hmv
    icases Hmv with ⟨%s, -, #Hs⟩
    iexists s; iexact Hs
  · iunfold isMvccWatchable at Hmv
    icases Hmv with ⟨%s, %st, %γw, %γp, %Hk, #Hws, -, -⟩
    iexists st
    ihave #Hs := isWatchableStore_isStore s st γw $$ Hws
    obtain ⟨-, hγ⟩ := Hk
    rw [← hγ]
    iexact Hs

/-- **The backend share is fractional** (`persistent.law`'s last conjunct): the token's and the
writer's fragment's parts split and join, the two parts' physical names agreeing. -/
instance mvccBackend_fractional (γ : MvccName) (B : BkRef) (Pk : IProp GF) :
    Fractional (fun q => mvccBackend (GF := GF) γ q B Pk) where
  fractional q1 q2 := by
    unfold mvccBackend
    have ht := (dghostVar_fractional (GF := GF) ((γ : StoreNames).api).tok ()).fractional q1 q2
    have hq : (q1 + q2).half.half.half = q1.half.half.half + q2.half.half.half := by
      rw [Qp_half_add, Qp_half_add, Qp_half_add]
    constructor
    · iintro ⟨HF, %p, %o, %d, Hc, %Hd, #Hb⟩
      iunfold shareTok at HF
      icases ht.1 $$ HF with ⟨HF1, HF2⟩
      rw [hq]
      icases ((curAt_fractional (GF := GF) ((γ : StoreNames).withPhys p) o).fractional
        q1.half.half.half q2.half.half.half).1 $$ Hc with ⟨Hc1, Hc2⟩
      isplitl [HF1 Hc1]
      · iunfold shareTok; iframe HF1; iexists p, o, d; iframe Hc1 Hb; ipureintro; exact Hd
      · iunfold shareTok; iframe HF2; iexists p, o, d; iframe Hc2 Hb; ipureintro; exact Hd
    · iintro ⟨⟨HF1, %p, %o, %d, Hc1, %Hd, #Hb⟩, ⟨HF2, %p', %o', %d', Hc2, %Hd', -⟩⟩
      ihave %Hv := curAt_agree ((γ : StoreNames).withPhys p) ((γ : StoreNames).withPhys p') rfl
        _ _ o o' $$ [Hc1 Hc2]
      · iframe Hc1 Hc2
      obtain ⟨ho, hp⟩ := Hv
      have hp' : p = p' := hp
      subst hp' ho
      have hdd : d = d' := by
        have h1 := Hd.1; have h2 := Hd'.1; rw [h1] at h2; cases h2; rfl
      subst hdd
      iunfold shareTok at HF1 HF2
      isplitl [HF1 HF2]
      · iunfold shareTok; iapply ht.2; iframe HF1 HF2
      iexists p, o, d
      rw [hq]
      isplitl [Hc1 Hc2]
      · iapply ((curAt_fractional (GF := GF) ((γ : StoreNames).withPhys p) o).fractional
          q1.half.half.half q2.half.half.half).2
        iframe Hc1 Hc2
      iframe Hb
      ipureintro; exact Hd

/-- **`mvccBackend_agree.law`**: two shares hold parts of the store's current physical names,
which agree, so the same backend. -/
theorem mvccBackend_agree.law_holds : mvccBackend_agree.law (GF := GF) := by
  intro γ q q' B B' Pk Pk'
  unfold mvccBackend
  iintro ⟨⟨-, %p, %o, %d, Hc1, %Hd, -⟩, ⟨-, %p', %o', %d', Hc2, %Hd', -⟩⟩
  ihave %Hv := curAt_agree (((γ : StoreNames)).withPhys p) ((γ : StoreNames).withPhys p') rfl
    _ _ o o' $$ [Hc1 Hc2]
  · iframe Hc1 Hc2
  ipureintro
  obtain ⟨-, hp⟩ := Hv
  have hp' : p = p' := hp
  subst hp'
  obtain ⟨h1, -, rfl⟩ := Hd
  obtain ⟨h2, -, rfl⟩ := Hd'
  rw [h1] at h2
  cases h2
  rfl

end laws

section snapshot
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [bk_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`mvccImage_snapshot.law`** (see the file header): the client's update committed first (the
state unchanged, nothing pending), the writer frozen with the whole share (`writerInv_freezeNL`),
the snapshot taken with the frozen writer's state lent to the observation (`snapObs_M1`), the
writer thawed (`writerInv_thawNL`), the image from the observation (`imageOk_of_snapObsOk`) and the
frozen writer's certificate (the receipt). -/
theorem mvccImage_snapshot.law_holds : mvccImage_snapshot.law (GF := GF) := by
  intro hSnap kv
  intro (γ : StoreNames)
  intro B Pk qo R Q Φ
  iintro %Ψ ⟨#Hpkg, Hmv, HB, Ho, Hwb, HR, #HQ, HAU⟩ HΨ
  ihave ⟨%s, #Hs⟩ := isMvcc_store kv γ $$ Hmv
  iunfold mvccBackend at HB
  icases HB with ⟨HF, %p, %o, %d, Hcur, %Hd, #Hbk⟩
  obtain ⟨hpk, hcm, rfl⟩ := Hd
  simp only []
  have hk : ((γ : StoreNames).withPhys p).kb = some d := hpk
  ihave #Hs0 := Hs
  iunfold isStore at Hs0
  iNamed Hs0
  -- freeze the writer with the whole share (no later credit: the code is the call alone)
  imod writerInv_freezeNL s ((γ : StoreNames).withPhys p) (γ : StoreNames).api rfl _ o $$
    [Hwi] HF Hcur with ⟨HT, Hfz, Hcur⟩
  · rw [show writerInv (GF := GF) s ((γ : StoreNames).withPhys p) = writerInv s γ from rfl]
    iexact Hwi
  -- the client's update at the frozen writer's state: committed now, the state unchanged
  ihave Hst : iprop(|={⊤}=> ∃ (σ : MvccState) (bb : Bool), Φ σ ∗
      snapFrozen s ((γ : StoreNames).withPhys p) σ bb ∗ ⌜MvccReachable σ⌝) $$ [HT HAU Hfz]
  · ihave HAU := atomic_update_mask_weaken (Eo2 := ⊤) CoPset.subseteq_top $$ HAU
    ihave Hacc := aupd_aacc $$ HAU
    unfold atomic_acc
    imod Hacc with Hacc
    isimp only [texist_cons, texist_nil, Std.Tele.app, ULift.down] at Hacc
    icases Hacc with ⟨%σ, ⟨Hσ, %Hpn⟩, Hucl⟩
    icases Hucl with ⟨-, Hcommit⟩
    isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at Hcommit
    iunfold mvccState at Hσ
    iunfold mvccStateI at Hσ
    icases Hσ with ⟨Ha, Hp, Hcr, Hnl, %Hreach⟩
    iunfold writerTaken at HT
    icases HT with (⟨HwL, HwR⟩ | HK)
    · ihave HwL := later_mono (writerL_split s ((γ : StoreNames).withPhys p)).1 $$ HwL
      icases HwL with ⟨%L, >Hwv, >HY, >Hcert, HLR⟩
      ihave HY := (slotY_some (γ := (γ : StoreNames).withPhys p) rfl L).1 $$ HY
      iunfold writerAbs at HY
      icases HY with ⟨%c, Hac, Hpw⟩
      iunfold absPart at Ha Hac
      simp only [StoreNames.withPhys_api]
      icombine Ha Hac gives %Hag
      obtain ⟨-, Hag⟩ := Hag
      have hL : L = σ.log := (Prod.mk.inj Hag).1.symm
      have hc : c = σ.crev := (Prod.mk.inj Hag).2.symm
      subst hL hc
      imod Hcommit $$ [Ha Hp Hcr Hnl] with HΦσ
      · iunfold mvccState
        iunfold mvccStateI
        iunfold absPart
        iframe
        ipureintro; exact Hreach
      imodintro
      iexists σ, true
      iframe HΦσ
      isplitl
      · iunfold snapFrozen
        simp only [StoreNames.withPhys_api]
        isplitl [Hfz]
        · iexact Hfz
        simp only [↓reduceIte]
        iframe Hwv Hcert HLR HwR
        iapply (slotY_some (γ := (γ : StoreNames).withPhys p) rfl σ.log).2
        iunfold writerAbs
        iexists σ.crev
        simp only [StoreNames.withPhys_api]
        isplitl [Hac]
        · iunfold absPart; iexact Hac
        · iexact Hpw
      · ipureintro; exact Hreach
    · imod Hcommit $$ [Ha Hp Hcr Hnl] with HΦσ
      · iunfold mvccState
        iunfold mvccStateI
        iframe
        ipureintro; exact Hreach
      imodintro
      iexists σ, false
      iframe HΦσ
      isplitl
      · iunfold snapFrozen
        simp only [StoreNames.withPhys_api]
        isplitl [Hfz]
        · iexact Hfz
        simp only [Bool.false_eq_true, ↓reduceIte]
        iexact HK
      · ipureintro; exact Hreach
  imod Hst with ⟨%σ, %bb, HΦσ, HFR, %Hreach⟩
  -- the snapshot, the frozen writer's state lent to the observation
  iapply wp_fupd
  iapply (hSnap d.γB d.P (mvccW d.gx) Pk d.be qo
    iprop(R ∗ snapFrozen s ((γ : StoreNames).withPhys p) σ bb)
    (fun vd dd r v => Q dd r ∧ bb = true ∧ snapObsOk σ.log σ.crev vd v)) $$ [Ho Hwb HR HFR]
  · iframe Hpkg Hbk Ho Hwb HR HFR
    iintro !> %vd %dd %r %v %X ⟨HR', HFR'⟩ HW HPk Hva Hdl Hhk Hrb Hfk
    ihave %H1 := HQ $$ %dd %r HR' HPk Hhk Hrb
    ihave %H2 := snapObs_M1 s ((γ : StoreNames).withPhys p) d hk hcm σ Hreach bb vd X v $$
      [HFR' HW Hva Hdl Hfk]
    · iframe
    ipureintro; exact ⟨H1, H2.1, H2.2⟩
  iintro !> %sp %D ⟨Hsn, Ho, ⟨HR, HFR⟩, -, %HQD⟩
  obtain ⟨hQ, hbb, hobs⟩ := HQD
  subst hbb
  iunfold snapFrozen at HFR
  simp only [↓reduceIte]
  icases HFR with ⟨Hfz, Hwv, HY, #Hcert, HLR, HwR⟩
  -- thaw
  ihave HT : iprop(▷ writerTaken s ((γ : StoreNames).withPhys p)) $$ [Hwv HY HLR HwR]
  · inext
    iunfold writerTaken
    ileft
    isplitl [Hwv HY HLR]
    · iapply (writerL_split s ((γ : StoreNames).withPhys p)).2
      iexists σ.log
      iframe Hwv HY HLR Hcert
    · iexact HwR
  simp only [StoreNames.withPhys_api]
  imod writerInv_thawNL s ((γ : StoreNames).withPhys p) (γ : StoreNames).api rfl _ o $$
    [Hwi] HT Hfz Hcur with ⟨HF, Hcur⟩
  · rw [show writerInv (GF := GF) s ((γ : StoreNames).withPhys p) = writerInv s γ from rfl]
    iexact Hwi
  imodintro
  iapply HΨ
  iframe Hsn Ho HR
  isplitl [HF Hcur]
  · iunfold mvccBackend
    iframe HF
    iexists p, o, d
    iframe Hcur Hbk
    ipureintro; exact ⟨hpk, hcm, rfl⟩
  isplitr
  · ipureintro; exact hQ
  iunfold idxCert at Hcert
  icases Hcert with ⟨-, %Hlwf, -, #Hrc⟩
  obtain ⟨u, hu⟩ := imageOk_of_snapObsOk σ Hreach ⟨Hlwf.2.1, Hlwf.2.2⟩ d.P
    (by simp [KBReal.P]) D hobs
  iexists σ, u
  iframe HΦσ
  iunfold mvccImage
  iframe Hrc
  ipureintro; exact hu

end snapshot

#print axioms mvccImage_fresh.law_holds
#print axioms mvccImage_snapshot.law_holds
#print axioms mvccBackend_agree.law_holds
#print axioms mvccBackend_fractional

end api
end mvcc
end EtcdGrove
end Perennial
