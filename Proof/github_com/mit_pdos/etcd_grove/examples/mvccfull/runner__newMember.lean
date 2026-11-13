/- Lean-first (no Rocq counterpart). The proof of `runner.newMember`: proved.

The outline: the struct allocated; the closure (`hookOk`'s triple: `applying.Load`,
`saved.Load`, `saved.Store`); the atomics' stores; the ghost names (`ghostVar`s, `monoNat`s) and
`memberCarry` at `mvccStart` (`histOkM` against `hist0`, `onceUpToAll` of the empty log);
`mvccImage_fresh.law`; `open` at `n = 0` (its `Ops ≤ k` the post's; `ops.length < 2 ^ 38` at the
empty log); the `regs` invariant.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__newMember
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__open
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.OpenLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem runner.newMember.wp_proof
    (hfresh : mvccImage_fresh.law (GF := GF))
    (wp_open : runner.open.spec (GF := GF) (hG := hG)) :
    runner.newMember.spec (GF := GF) (hG := hG) := by
  intro _ _ x ks cfg wr h γh id path hid0 hid2 hdbo hck hlim hcbl
  haveI : ∀ N l, Persistent (ctrInv (GF := GF) N l) := by intro N l; unfold ctrInv; infer_instance
  wp_start as ⟨#Hctx, #Hks, #Hvoff, Htok, Hrd, #Hlb, Hfile⟩
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull $$ []
  · iunfold writerCtx at Hctx; icases Hctx with ⟨#Hrn, -⟩; iunfold rnCtx at Hrn
    icases Hrn with ⟨#H, -⟩; iexact H
  wp_auto
  irename «$r0» => Hmr
  generalize «$r0_ptr» = mp at *
  iStructNamedSuffix Hmr "M"
  try simp only []
  ihave HrevLo := ownInt64_of_zero (mF go!"revLo" mp) $$ revLoM
  ihave HrevHi := ownInt64_of_zero (mF go!"revHi" mp) $$ revHiM
  ihave HcmpLo := ownInt64_of_zero (mF go!"cmpLo" mp) $$ cmpLoM
  ihave HcmpHi := ownInt64_of_zero (mF go!"cmpHi" mp) $$ cmpHiM
  ihave Happ := ownInt64_of_zero (mF go!"applying" mp) $$ applyingM
  ihave Hsav := ownInt64_of_zero (mF go!"saved" mp) $$ savedM
  ihave Hregs := ownInt64_of_zero (mF go!"regs" mp) $$ regsM
  wp_apply_core sync.atomic.Int64.wp_Store (mF go!"revLo" mp) _ $$ [] [-]
  · iPkgInit
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ from Std.LawfulSet.empty_subset)
  iintro Hcl
  inext
  iexists _
  iframe HrevLo
  iintro HrevLo
  imod Hcl with -
  imodintro
  (try wp_auto)
  wp_apply_core sync.atomic.Int64.wp_Store (mF go!"revHi" mp) _ $$ [] [-]
  · iPkgInit
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ from Std.LawfulSet.empty_subset)
  iintro Hcl
  inext
  iexists _
  iframe HrevHi
  iintro HrevHi
  imod Hcl with -
  imodintro
  (try wp_auto)
  wp_apply_core sync.atomic.Int64.wp_Store (mF go!"cmpLo" mp) _ $$ [] [-]
  · iPkgInit
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ from Std.LawfulSet.empty_subset)
  iintro Hcl
  inext
  iexists _
  iframe HcmpLo
  iintro HcmpLo
  imod Hcl with -
  imodintro
  (try wp_auto)
  wp_apply_core sync.atomic.Int64.wp_Store (mF go!"cmpHi" mp) _ $$ [] [-]
  · iPkgInit
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ from Std.LawfulSet.empty_subset)
  iintro Hcl
  inext
  iexists _
  iframe HcmpHi
  iintro HcmpHi
  imod Hcl with -
  imodintro
  (try wp_auto)
  -- the hook's closure: its triple
  ipersist m
  ipersist hookM
  ipersist idM
  generalize hf : (func.mk BAnon BAnon _ : GoFunc) = f at *
  ihave HhookOk : hookOk mp f $$ []
  · iunfold hookOk
    isplitr
    · ipureintro; rw [← hf]; nofun
    iintro !> %i %s
    unfold mvcc.api.hookRun
    split
    · exfalso; rename_i h; rw [← hf] at h; cases h
    iintro !> !> %Φ' ⟨-, Hpre⟩ HΦ'
    iunfold hookPre at Hpre
    icases Hpre with ⟨Ha, Hs, %Hsi⟩
    rw [← hf, ← recv_eq_func_mk]
    wp_auto
    wp_apply_core sync.atomic.Int64.wp_Load (mF go!"applying" mp) (DFrac.own 1) $$ [] [-]
    · iPkgInit
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ from Std.LawfulSet.empty_subset)
    iintro Hcl
    inext
    iexists i
    iframe Ha
    iintro Ha
    imod Hcl with -
    imodintro
    wp_auto
    wp_apply_core sync.atomic.Int64.wp_Load (mF go!"saved" mp) (DFrac.own 1) $$ [] [-]
    · iPkgInit
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ from Std.LawfulSet.empty_subset)
    iintro Hcl
    inext
    iexists s
    iframe Hs
    iintro Hs
    imod Hcl with -
    imodintro
    wp_auto
    wp_if_destruct
    · wp_apply_core sync.atomic.Int64.wp_Store (mF go!"saved" mp) i $$ [] [-]
      · iPkgInit
      iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ from Std.LawfulSet.empty_subset)
      iintro Hcl
      inext
      iexists s
      iframe Hs
      iintro Hs
      imod Hcl with -
      imodintro
      (try wp_auto)
      iapply HΦ'
      iunfold hookPost
      iframe
    · (try wp_auto)
      have : s = i := by word
      subst this
      iapply HΦ'
      iunfold hookPost
      iframe
  -- the member's ghost state at the fresh store; the `regs` counter's invariant
  imod ghostVar_alloc (GF := GF) mvccStart with ⟨%γσ, Hσ⟩
  icases (ghostVar_split_half γσ 1 _).1 $$ Hσ with ⟨Hσ1, Hσ2⟩
  imod ghostVar_alloc (GF := GF) ((W64 1, W64 1, W64 (-1), W64 (-1)) : Bnd) with ⟨%γb, Hb⟩
  icases (ghostVar_split_half γb 1 _).1 $$ Hb with ⟨Hb1, Hb2⟩
  imod mono_nat_own_alloc (GF := GF) mvccStart.rev with ⟨%γr, Hr, -⟩
  imod mono_nat_own_alloc (GF := GF) (Int.toNat (mvccStart.crev + 1)) with ⟨%γc, Hc, -⟩
  imod mono_nat_own_alloc (GF := GF) mvccStart.notifiedLog.length with ⟨%γn, Hn, -⟩
  imod inv_alloc (sCtrN .@ "regs") ⊤
      (∃ v : w64, sync.atomic.ownInt64 (GF := GF) (mF go!"regs" mp) (DFrac.own 1) v) $$ [Hregs]
    with #Hreginv
  · inext; iexists _; iexact Hregs
  imod hfresh ∅ (fun _ => rfl) rfl rfl with Himg
  -- the model's facts at the empty log
  ihave %Hsorted : ⌜ks.Pairwise go.GoStringLt⌝ $$ []
  · iunfold writerCtx at Hctx; icases Hctx with ⟨#Hrn, -⟩; iunfold rnCtx at Hrn
    icases Hrn with ⟨-, -, #Hkeys, -⟩; iunfold runnerKeys at Hkeys
    icases Hkeys with ⟨%keys, -, -, %Hs, -⟩; ipureintro; exact Hs
  have hlog0 : logOk ks ([] : List OpM) := fun i o h => by simp at h
  have hσh := logOk_hist ks Hsorted [] hlog0 0 0 (Nat.le_refl _) (Nat.le_refl _)
  have honce := logOk_once ks Hsorted [] hlog0 0
  rw [σOf_zero] at hσh honce
  have hH0 : histAt ks ([] : List OpM) 0 = hist0 := by simp only [histAt, runM_zero]; rfl
  rw [hH0] at hσh
  have hidE : W64 ((sint.nat id : Nat) : Int) = id := by
    have : sint.nat id = (sint.Z id).toNat := rfl
    word
  have hr0 : revAfter ks ([] : List OpM) 0 = 1 := by simp only [revAfter, runM_zero]; rfl
  have hc0 : cmpAfter ks ([] : List OpM) 0 = -1 := by simp only [cmpAfter, runM_zero]; rfl
  have hl0 : leasesAfter ks ([] : List OpM) 0 = [] := by simp only [leasesAfter, runM_zero]; rfl
  wp_apply (wp_open x ks cfg wr h γh [] (sint.nat id) mp ⟨γσ, γr, γc, γn, γb⟩ f 0 path ∅ false
      (W64 1, W64 1, W64 (-1), W64 (-1)) hist0 GoInterface.nil GoInterface.nil GoInterface.nil hlog0
      (Nat.le_refl _) (by simp) hdbo hck hlim hcbl)
    $$ [Htok Hrd HhookOk pathM beM leM kvM revM cmpM leasesM Hfile Himg Hσ1 Hσ2 Hb1 Hb2 HrevLo HrevHi
      HcmpLo HcmpHi Hr Hc Hn]
    as ⟨Htok, Hrd, %v, %k, %Hv, Hcore⟩
  · simp only [σOf_zero, hr0, hc0, hl0, hH0, hidE]
    iframe #; iframe
    isplitl []
    · isplitl []
      · iapply (ownSlice_nil (V := w64) (GF := GF) (DFrac.own 1))
      · iapply (ownSliceCap_nil (V := w64) (GF := GF))
    isplitr
    · ipureintro
      refine ⟨[], ?_, rfl, fun _ h => by cases h⟩
      have hLe : ((backend.rbData (mvccrand.rcP (limOf cfg)) ∅).lookup go!"lease").getD ∅ = ∅ := rfl
      show backend.bktEnts (((backend.rbData (mvccrand.rcP (limOf cfg)) ∅).lookup go!"lease").getD ∅) = _
      rw [hLe]; simp [backend.bktEnts]
    iunfold memberCarry
    iframe
    isplitr
    · iexact Hlb
    ipureintro
    have hrev : mvccStart.rev = 1 := rfl
    have hnl : mvccStart.notifiedLog.length = 2 := rfl
    have hcr : mvccStart.crev = -1 := rfl
    rw [hrev, hnl, hcr]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hσh.2.1, honce⟩ <;> first | decide | word
  obtain ⟨hv0, hvp, -, hk⟩ := Hv
  iapply HΦ
  iframe Htok Hrd
  iexists ⟨γσ, γr, γc, γn, γb⟩, f, v, k
  isplitr
  · ipureintro; exact ⟨hv0, hvp, hk⟩
  iframe streamsM
  isplitl [Hcore opsM Happ Hsav]
  · iintro %ops
    iunfold memW
    rw [memCore_ops0 ks γh ops [] _ mp _ f v 1 mvccReaderN k hv0]
    iframe Hcore
    isplitl [opsM]
    · rw [hv0, show (W64 ((0 : Nat) : Int)) = (0 : w64) from rfl]; iexact opsM
    iexists W64 0, W64 0
    iunfold hookPre
    iframe
    ipureintro; rw [hv0]; decide
  · iunfold ctrInv; iexact Hreginv

end proof

end mvccfull
end EtcdGrove
end Perennial
