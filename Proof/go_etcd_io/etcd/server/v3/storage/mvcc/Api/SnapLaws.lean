/-
**The snapshot image's laws of mvcc's API** (stage 2, M2, 2026-11-05: `notes/mvcc-api-risk.md`,
M2), over the sealed definitions (`Api.lean`: `mvccImage`, its pure part `snap.imageOk`,
`Api/SnapImage.lean`). Lean-first (no Rocq counterpart).
- `mvccImage_fresh.law_holds`: a fresh backend's data is the empty history's image, its receipt
  `⧖ 0` allocated (`preceipt_zero`);
- `mvccW_alloc.law_holds` (M3): the registration slot, unset, in two halves.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.EtcdBackend
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.EtcdBackend
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
  icases Hmv with #(⟨Hmv, %Hwq⟩ | Hmv)
  · iunfold isMvccPlain at Hmv
    icases Hmv with ⟨%s, -, #Hs, -, -⟩
    iexists s; iexact Hs
  · iunfold isMvccWatchable at Hmv
    icases Hmv with ⟨%s, %st, %γw, %Hk, #Hws, -, -⟩
    iexists st
    ihave #Hs := isWatchableStore_isStore s st γw $$ Hws
    obtain ⟨-, hγ⟩ := Hk
    rw [← hγ]
    iexact Hs

/-- **The backend share is fractional** (`persistent.law`'s last conjunct): the token's and the
writer's fragment's parts split and join, the two parts' physical names agreeing. -/
instance mvccBackend_fractional (γ : MvccName) (B : MvccStorage) (Pk : IProp GF) :
    Fractional (fun q => mvccBackend (GF := GF) γ q B Pk) where
  fractional q1 q2 := by
    unfold mvccBackend
    have ht := (dghostVar_fractional (GF := GF) ((γ : StoreNames).api).tok ()).fractional q1 q2
    have hq : (q1 + q2).half.half.half = q1.half.half.half + q2.half.half.half := by
      rw [Qp_half_add, Qp_half_add, Qp_half_add]
    constructor
    · iintro ⟨HF, %p, %o, %d, Hc, %Hd, #Hb, #Hrg, #Hhp, #Hwt⟩
      iunfold shareTok at HF
      icases ht.1 $$ HF with ⟨HF1, HF2⟩
      rw [hq]
      icases ((curAt_fractional (GF := GF) ((γ : StoreNames).withPhys p) o).fractional
        q1.half.half.half q2.half.half.half).1 $$ Hc with ⟨Hc1, Hc2⟩
      isplitl [HF1 Hc1]
      · iunfold shareTok; iframe HF1; iexists p, o, d; iframe Hc1 Hb Hrg Hhp Hwt; ipureintro; exact Hd
      · iunfold shareTok; iframe HF2; iexists p, o, d; iframe Hc2 Hb Hrg Hhp Hwt; ipureintro; exact Hd
    · iintro ⟨⟨HF1, %p, %o, %d, Hc1, %Hd, #Hb, #Hrg, #Hhp, #Hwt⟩, ⟨HF2, %p', %o', %d', Hc2, %Hd', -, -, -⟩⟩
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
      iframe Hb Hrg Hhp Hwt
      ipureintro; exact Hd

/-- **`mvccBackend_agree.law`**: two shares hold parts of the store's current physical names,
which agree, so the same backend. -/
theorem mvccBackend_agree.law_holds : mvccBackend_agree.law (GF := GF) := by
  intro γ q q' B B' Pk Pk'
  unfold mvccBackend
  iintro ⟨⟨-, %p, %o, %d, Hc1, %Hd, -, -, -⟩, ⟨-, %p', %o', %d', Hc2, %Hd', -, -, -⟩⟩
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

/-- **`mvccBackend_isBackend.law`** (the server's migration, 2026-11-05): the share's body records
`isBackend` at `mvccW d.gx`. -/
theorem mvccBackend_isBackend.law_holds : mvccBackend_isBackend.law (GF := GF) := by
  intro γ q bk Pk
  unfold mvccBackend
  iintro ⟨-, %p, %o, %d, -, %Hd, #Hb, -, -⟩
  have hd : d = bk := Hd.2.2
  subst hd
  unfold mvccW
  iexact Hb

/-- **`mvccW_alloc.law`** (M3, 2026-11-05): the registration slot allocated unset, its halves the
right to register (`lateReg`) and the batch lock's late-bound resource (`lateW`'s unset branch). -/
theorem mvccW_alloc.law_holds : mvccW_alloc.law (GF := GF) := by
  iintro
  imod dghostVar_alloc (GF := GF) (none : Option (Loc × StoreNames)) with ⟨%gx, H⟩
  rw [dfrac_own_half_half 1]
  icases (dghostVar_split (GF := GF) gx (none : Option (Loc × StoreNames)) (DFrac.own (1 : Qp).half)
    (DFrac.own (1 : Qp).half)) $$ H with ⟨H1, H2⟩
  imodintro
  iexists gx
  unfold mvccWReg mvccW lateReg lateW
  iframe H1
  ileft; iexact H2

/-- **`backendRest_open.law`** (the tester's migration, 2026-11-06, G1): `backendRest` is its parts. -/
theorem backendRest_open.law_holds : backendRest_open.law (GF := GF) := by
  intro γB P K b D
  unfold backendRest
  exact .rfl

/-- **`errVars.law`** (the tester's migration, 2026-11-06, G2): the error variables' facts of the
package's initialization (`mvccInit`). -/
theorem errVars.law_holds : errVars.law (GF := GF) := by
  iintro #Hpkg
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, H1, H2, H3, -⟩
  iframe H1 H2 H3

end laws

section snapshot
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [bk_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`mvccImage_snapshot.law`** (see the file header): the writer frozen with the whole share, the
registration lent if pending (`writerInv_freezeR`); the client's update committed at once (the state
unchanged, nothing pending), the frozen writer's slot agreeing with `mvccState`; the snapshot taken
with the frozen writer's state lent to the observation (`snapObs`: the batch lock's writer's
resource pins the tracked compaction); the registration given back (`reg_unlend`) and the writer
thawed (`writerInv_thawNL`); the image from the observation (`imageOk_of_snapObsOk`) and the
frozen writer's certificate (the receipt). -/
theorem mvccImage_snapshot.law_holds : mvccImage_snapshot.law (GF := GF) := by
  intro hSnap _ kv
  intro (γ : StoreNames)
  intro bk Pk qo R Q Φ
  iintro %Ψ ⟨#Hpkg, Hmv, HB, Ho, Hwb, Htok, HR, #HQ, HAU⟩ HΨ
  ihave ⟨%s, #Hs⟩ := isMvcc_store kv γ $$ Hmv
  iunfold mvccBackend at HB
  icases HB with ⟨HF, %p, %o, %d, Hcur, %Hd, #Hbk, #⟨%s', #Hrg⟩, #Hhp, #Hwt⟩
  obtain ⟨hpk, hcm, hd⟩ := Hd
  have hd' : d = bk := hd
  subst hd'
  simp only []
  have hk : ((γ : StoreNames).withPhys p).kb = some d := hpk
  ihave #Hs0 := Hs
  iunfold isStore at Hs0
  iNamed Hs0
  -- freeze the writer with the whole share, the registration lent if pending (no later credit)
  imod writerInv_freezeR s s' ((γ : StoreNames).withPhys p) (γ : StoreNames).api rfl d hk _ o $$
    [Hwi] Hrg HF Hcur with ⟨Hcur, HT⟩
  · rw [show writerInv (GF := GF) s ((γ : StoreNames).withPhys p) = writerInv s γ from rfl]
    iexact Hwi
  -- the client's update at the frozen writer's state: committed now, the state unchanged
  ihave Hst : iprop(|={⊤}=> ∃ (σ : MvccState) (bb : Bool), Φ σ ∗
      snapFrozen s s' ((γ : StoreNames).withPhys p) σ bb ∗ ⌜MvccReachable σ⌝) $$ [HT HAU]
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
    icases Hσ with ⟨Ha, Hp, Hcr, Hnl, %Hreach, #Hrcm⟩
    icases HT with (⟨⟨HwL, HwR⟩, Hfz, HRg⟩ | ⟨Hfz, HK⟩)
    rotate_left 1
    · icases HK with ⟨>HK, >Hd, >Hreg⟩
      imod Hcommit $$ [Ha Hp Hcr Hnl] with HΦσ
      · iunfold mvccState
        iunfold mvccStateI
        iframe
        iframe Hrcm; ipureintro; exact Hreach
      imodintro
      iexists σ, false
      iframe HΦσ
      isplitl
      · iunfold snapFrozen
        simp only [StoreNames.withPhys_api, Bool.false_eq_true, ↓reduceIte]
        iframe Hfz HK Hd Hreg
      · ipureintro; exact Hreach
    · ihave HwL := later_mono (writerL_split s ((γ : StoreNames).withPhys p)).1 $$ HwL
      icases HwL with ⟨%L, >Hwv, >HY, >Hcert, HLR⟩
      icases (slotY_some (γ := (γ : StoreNames).withPhys p) rfl L).1 $$ HY with ⟨%c, Hac, Hpw, Hrc, Hwc⟩
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
        iframe Hrcm; ipureintro; exact Hreach
      imodintro
      iexists σ, true
      iframe HΦσ
      isplitl
      · iunfold snapFrozen
        simp only [StoreNames.withPhys_api, ↓reduceIte]
        iframe Hwv Hcert HLR HwR Hpw Hrc Hwc Hfz HRg
        iunfold absPart; iexact Hac
      · ipureintro; exact Hreach
  imod Hst with ⟨%σ, %bb, HΦσ, HFR, %Hreach⟩
  -- the snapshot, the frozen writer's state lent to the observation
  iapply wp_fupd
  iapply (hSnap d.γB d.P (lateW d.gx) Pk d.be qo
    iprop(R ∗ snapFrozen s s' ((γ : StoreNames).withPhys p) σ bb)
    (fun vd dd r v => Q dd r ∧ bb = true ∧ snapObsOk σ.log σ.crev vd v)) $$ [Ho Hwb Htok HR HFR]
  · iframe Hpkg Hbk Ho Hwb Htok HR HFR
    iintro !> %vd %dd %r %v %X ⟨HR', HFR'⟩ HW HPk Hva Hdl Hhk Hrb Hfk
    ihave %H1 := HQ $$ %dd %r HR' HPk Hhk Hrb
    ihave %H2 := snapObs s s' ((γ : StoreNames).withPhys p) d hk hcm σ bb vd X v $$
      [HFR' HW Hva Hdl Hfk]
    · iframe
    ipureintro; exact ⟨H1, H2.1, H2.2⟩
  iintro !> %sp %D ⟨Hsn, Ho, ⟨HR, HFR⟩, -, %HQD⟩
  obtain ⟨hQ, hbb, hobs⟩ := HQD
  subst hbb
  iunfold snapFrozen at HFR
  simp only [↓reduceIte]
  icases HFR with ⟨Hwv, Hac, Hpw, Hrc, Hwc, #Hcert, HLR, HwR, Hfz, HRg⟩
  -- the registration given back
  ihave Hfz2 : iprop(|={⊤}=> ghostVar ((γ : StoreNames).withPhys p).api.frz (1 : Qp).half.half true)
    $$ [HRg]
  · icases HRg with (⟨-, Hfz2⟩ | ⟨Ht, HWr⟩)
    · imodintro; iexact Hfz2
    · iapply reg_unlend s' ((γ : StoreNames).withPhys p) d hk ⊤ (by solve_ndisj) $$ Hrg
      iframe Ht HWr
  imod Hfz2 with Hfz2
  ihave Hfz := (ghostVar_split_half (GF := GF) ((γ : StoreNames).withPhys p).api.frz
    (1 : Qp).half true).2 $$ [Hfz Hfz2]
  · iframe Hfz Hfz2
  -- thaw
  ihave HT : iprop(▷ writerTaken s ((γ : StoreNames).withPhys p)) $$ [Hwv Hac Hpw Hrc Hwc HLR HwR]
  · inext
    iunfold writerTaken
    ileft
    isplitl [Hwv Hac Hpw Hrc Hwc HLR]
    · iapply (writerL_split s ((γ : StoreNames).withPhys p)).2
      iexists σ.log
      iframe Hwv HLR Hcert
      iapply (slotY_some (γ := (γ : StoreNames).withPhys p) rfl σ.log).2
      iexists σ.crev
      iframe Hac Hpw Hrc Hwc
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
    isplitr
    · ipureintro; exact ⟨hpk, hcm, rfl⟩
    iframe Hhp Hwt
    iexists s'; iexact Hrg
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

section stop
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- A pure consequence, the resources kept. -/
private theorem keep_pure {P : IProp GF} {φ : Prop} (h : P ⊢ ⌜φ⌝) : P ⊢ P ∗ ⌜φ⌝ :=
  (and_intro .rfl h).trans persistent_and_sep_mp

/-- **`mvccImage_stop.law`** (2026-11-07; see its statement): as `mvccImage_snapshot.law_holds`,
with the stopped lock's resources in place of the snapshot's observation. The writer frozen with
the whole share, the registration lent if pending (`writerInv_freezeR`); the client's update
committed at once, the frozen writer's slot agreeing with `mvccState`; the stopped lock's resource
(the writer's, `lateW`), its view quarter with the deleted entries (`viewAtD`, `dlsOwn`) and its
half of the compaction keys' values observed with the frozen writer's state (`snapObs`, kept); the
registration given back (`reg_unlend`), the writer thawed (`writerInv_thawNL`); the image from the
observation (`imageOk_of_snapObsOk`) and the frozen writer's certificate (the receipt). -/
theorem mvccImage_stop.law_holds : mvccImage_stop.law (GF := GF) := by
  intro kv
  intro (γ : StoreNames)
  intro bk Pk D Φ
  iintro ⟨Hmv, HB, Hsv, HAU⟩
  ihave ⟨%s, #Hs⟩ := isMvcc_store kv γ $$ Hmv
  iunfold mvccBackend at HB
  icases HB with ⟨HF, %p, %o, %d, Hcur, %Hd, #Hbk, #⟨%s', #Hrg⟩, #Hhp, #Hwt⟩
  obtain ⟨hpk, hcm, hd⟩ := Hd
  have hd' : d = bk := hd
  subst hd'
  simp only []
  have hk : ((γ : StoreNames).withPhys p).kb = some d := hpk
  ihave #Hs0 := Hs
  iunfold isStore at Hs0
  iNamed Hs0
  -- freeze the writer with the whole share, the registration lent if pending (no later credit)
  imod writerInv_freezeR s s' ((γ : StoreNames).withPhys p) (γ : StoreNames).api rfl d hk _ o $$
    [Hwi] Hrg HF Hcur with ⟨Hcur, HT⟩
  · rw [show writerInv (GF := GF) s ((γ : StoreNames).withPhys p) = writerInv s γ from rfl]
    iexact Hwi
  -- the client's update at the frozen writer's state: committed now, the state unchanged
  ihave Hst : iprop(|={⊤}=> ∃ (σ : MvccState) (bb : Bool), Φ σ ∗
      snapFrozen s s' ((γ : StoreNames).withPhys p) σ bb ∗ ⌜MvccReachable σ⌝) $$ [HT HAU]
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
    icases Hσ with ⟨Ha, Hp, Hcr, Hnl, %Hreach, #Hrcm⟩
    icases HT with (⟨⟨HwL, HwR⟩, Hfz, HRg⟩ | ⟨Hfz, HK⟩)
    rotate_left 1
    · icases HK with ⟨>HK, >Hd, >Hreg⟩
      imod Hcommit $$ [Ha Hp Hcr Hnl] with HΦσ
      · iunfold mvccState
        iunfold mvccStateI
        iframe
        iframe Hrcm; ipureintro; exact Hreach
      imodintro
      iexists σ, false
      iframe HΦσ
      isplitl
      · iunfold snapFrozen
        simp only [StoreNames.withPhys_api, Bool.false_eq_true, ↓reduceIte]
        iframe Hfz HK Hd Hreg
      · ipureintro; exact Hreach
    · ihave HwL := later_mono (writerL_split s ((γ : StoreNames).withPhys p)).1 $$ HwL
      icases HwL with ⟨%L, >Hwv, >HY, >Hcert, HLR⟩
      icases (slotY_some (γ := (γ : StoreNames).withPhys p) rfl L).1 $$ HY with ⟨%c, Hac, Hpw, Hrc, Hwc⟩
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
        iframe Hrcm; ipureintro; exact Hreach
      imodintro
      iexists σ, true
      iframe HΦσ
      isplitl
      · iunfold snapFrozen
        simp only [StoreNames.withPhys_api, ↓reduceIte]
        iframe Hwv Hcert HLR HwR Hpw Hrc Hwc Hfz HRg
        iunfold absPart; iexact Hac
      · ipureintro; exact Hreach
  imod Hst with ⟨%σ, %bb, HΦσ, HFR, %Hreach⟩
  -- the stopped lock's resources observed with the frozen writer's state, kept
  iunfold backend.bStopView at Hsv
  icases Hsv with ⟨HW, HPk, ⟨%X, Hva, Hdl⟩, Hhk, Hrb, Hfkd, HfR⟩
  unfold mvccW
  icases keep_pure (snapObs s s' ((γ : StoreNames).withPhys p) d hk hcm σ bb
    (backend.sData d.P D) X (backend.fkVals D)) $$ [HFR HW Hva Hdl Hfkd]
    with ⟨⟨HFR, HW, Hva, Hdl, Hfkd⟩, %Hobs⟩
  · iframe HFR HW Hva Hdl Hfkd
  obtain ⟨hbb, hobs⟩ := Hobs
  subst hbb
  iunfold snapFrozen at HFR
  simp only [↓reduceIte]
  icases HFR with ⟨Hwv, Hac, Hpw, Hrc, Hwc, #Hcert, HLR, HwR, Hfz, HRg⟩
  -- the registration given back
  ihave Hfz2 : iprop(|={⊤}=> ghostVar ((γ : StoreNames).withPhys p).api.frz (1 : Qp).half.half true)
    $$ [HRg]
  · icases HRg with (⟨-, Hfz2⟩ | ⟨Ht, HWr⟩)
    · imodintro; iexact Hfz2
    · iapply reg_unlend s' ((γ : StoreNames).withPhys p) d hk ⊤ (by solve_ndisj) $$ Hrg
      iframe Ht HWr
  imod Hfz2 with Hfz2
  ihave Hfz := (ghostVar_split_half (GF := GF) ((γ : StoreNames).withPhys p).api.frz
    (1 : Qp).half true).2 $$ [Hfz Hfz2]
  · iframe Hfz Hfz2
  -- thaw
  ihave HT : iprop(▷ writerTaken s ((γ : StoreNames).withPhys p)) $$ [Hwv Hac Hpw Hrc Hwc HLR HwR]
  · inext
    iunfold writerTaken
    ileft
    isplitl [Hwv Hac Hpw Hrc Hwc HLR]
    · iapply (writerL_split s ((γ : StoreNames).withPhys p)).2
      iexists σ.log
      iframe Hwv HLR Hcert
      iapply (slotY_some (γ := (γ : StoreNames).withPhys p) rfl σ.log).2
      iexists σ.crev
      iframe Hac Hpw Hrc Hwc
    · iexact HwR
  simp only [StoreNames.withPhys_api]
  imod writerInv_thawNL s ((γ : StoreNames).withPhys p) (γ : StoreNames).api rfl _ o $$
    [Hwi] HT Hfz Hcur with ⟨HF, Hcur⟩
  · rw [show writerInv (GF := GF) s ((γ : StoreNames).withPhys p) = writerInv s γ from rfl]
    iexact Hwi
  imodintro
  isplitl [HF Hcur]
  · iunfold mvccBackend
    iframe HF
    iexists p, o, d
    iframe Hcur Hbk
    isplitr
    · ipureintro; exact ⟨hpk, hcm, rfl⟩
    iframe Hhp Hwt
    iexists s'; iexact Hrg
  isplitl [HW HPk Hva Hdl Hhk Hrb Hfkd HfR]
  · iunfold backend.bStopView
    iframe HW HPk Hhk Hrb Hfkd HfR
    iexists X
    iframe Hva Hdl
  iunfold idxCert at Hcert
  icases Hcert with ⟨-, %Hlwf, -, #Hrc⟩
  obtain ⟨u, hu⟩ := imageOk_of_snapObsOk σ Hreach ⟨Hlwf.2.1, Hlwf.2.2⟩ d.P
    (by simp [KBReal.P]) D hobs
  iexists σ, u
  iframe HΦσ
  iunfold mvccImage
  iframe Hrc
  ipureintro; exact hu

end stop

#print axioms mvccImage_fresh.law_holds
#print axioms mvccImage_snapshot.law_holds
#print axioms mvccImage_stop.law_holds
#print axioms mvccBackend_agree.law_holds
#print axioms mvccBackend_fractional
#print axioms mvccBackend_isBackend.law_holds

end api
end mvcc
end EtcdGrove
end Perennial
