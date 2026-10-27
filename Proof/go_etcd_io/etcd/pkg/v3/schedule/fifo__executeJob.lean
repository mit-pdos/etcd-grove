/-
`(*fifo).executeJob`. Lean-first (2026-10-22, the scheduler translated with its body).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.schedule.fifo__executeJob
public import Proof.go_etcd_io.etcd.pkg.v3.schedule.Chain

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3 schedule

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.schedule.Assumptions]

theorem schedule.fifo.executeJob.wp_proof : schedule.fifo.executeJob.spec (GF := GF) (hG := hG) := by
  intro l γ F j Pre Prev Post upd
  wp_start as ⟨#Hf, Hrun, #Hjob, HPre, HPrev, Hfp⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold fifoIs at Hf
  iNamed Hf
  iunfold jobIs at Hjob
  icases Hjob with ⟨%jt, %Hj, #Hdo⟩
  subst Hj
  wp_apply wp_with_defer_recover as %defer %pnc Hdefer Hpnc
  (try wp_auto)
  iunfold jobDoSpec at Hdo
  wp_apply Hdo $$ [Hrun HPre HPrev] as ⟨Hrun, HPost⟩
  · iframe
    iexact Hisctx
  (try wp_auto)
  rw [sync.isCond_unseal] at *
  iunfold sync.isCondDef at Hcnd
  iNamed Hcnd
  cases upd with
  | true =>
    simp only [Bool.not_true, ↓reduceIte]
    (try wp_auto)
    wp_apply wp_recoverPanic $$ Hpnc as Hpnc
    (try wp_auto)
    iapply HΦ
    iframe
  | false =>
    simp only [Bool.not_false, Bool.false_eq_true, ↓reduceIte]
    (try wp_auto)
    wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlk, HI⟩
    iunfold fifoLockInv at HI
    iNamed HI
    iunfold finishPre at Hfp
    icases Hfp with ⟨%rs', Hrs', Hfrs⟩
    ihave %Hrr := dghostVar_agree F.w _ _ _ _ $$ Hrs Hrs'
    subst Hrr
    obtain ⟨Hpend, Hchain⟩ := Hjs
    ihave %Hlen := ownSlice_len $$ Hsl
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hsl
    rcases rs with _ | _ | k | _
    · iexfalso; iexact Hfrs
    · -- an untracked job: the baton stays
      obtain ⟨Hd, Hne⟩ := Hpend
      have hl1 : 1 ≤ sint.Z sl.len := by
        cases js with
        | nil => exact absurd rfl Hne
        | cons x xs => simp at Hlen; word
      (try wp_auto)
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, hl1, Hwf.2⟩)]
      (try wp_auto)
      icases ownSlice_slice_with_cap (W64 1) sl.len sl _ ⟨by word, by word, by word⟩
        $$ [Hsl Hcap] with ⟨-, Hsl, Hcap⟩
      · iframe
      wp_apply sync.Cond.wp_Broadcast
      · rw [sync.isCond_unseal]; unfold sync.isCondDef; iframe #
      (try wp_auto)
      imod dghostVar_update_halves RunSt.idle F.w _ _ $$ Hrs Hrs' with ⟨Hrs, Hrs'⟩
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hpend Hsl Hcap Hsch Hfin Hcf Hrs Hq Hitems Hbaton Hst]
      · inext
        iunfold fifoLockInv
        iexists slice.slice sl GoInterface (W64 1) sl.len, subslice (sint.nat (W64 1)) (sint.nat sl.len) js,
          items, RunSt.idle, L, b, cf, sc, fn + W64 1
        simp only [named]
        iframe
        isplitl []
        · ipureintro
          refine ⟨?_, Hchain⟩
          simp only [pendOk, subslice]
          rw [← Hd]
          have : sint.nat sl.len = js.length := by word
          rw [this, List.take_of_length_le (by simp)]
          rfl
        iunfold batonAt at Hbaton
        iunfold batonAt
        iexact Hbaton
      (try wp_auto)
      wp_apply wp_recoverPanic $$ Hpnc as Hpnc
      (try wp_auto)
      iapply HΦ
      iframe
    · -- a tracked job: its `Post` the baton at `k + 1`
      obtain ⟨Hd, Hne⟩ := Hpend
      have hl1 : 1 ≤ sint.Z sl.len := by
        cases js with
        | nil => exact absurd rfl Hne
        | cons x xs => simp at Hlen; word
      (try wp_auto)
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, hl1, Hwf.2⟩)]
      (try wp_auto)
      icases ownSlice_slice_with_cap (W64 1) sl.len sl _ ⟨by word, by word, by word⟩
        $$ [Hsl Hcap] with ⟨-, Hsl, Hcap⟩
      · iframe
      wp_apply sync.Cond.wp_Broadcast
      · rw [sync.isCond_unseal]; unfold sync.isCondDef; iframe #
      (try wp_auto)
      imod dghostVar_update_halves RunSt.idle F.w _ _ $$ Hrs Hrs' with ⟨Hrs, Hrs'⟩
      icases Hfrs with ⟨%ps, #Hidx, #Hps⟩
      iunfold batonAt at Hbaton
      icases Hbaton with %Hb
      ihave %HLps := mono_list_auth_idx_lookup γ.jobs _ L (k + 1) ps $$ Hq Hidx
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hpend Hsl Hcap Hsch Hfin Hcf Hrs Hq Hitems HPost Hst]
      · inext
        iunfold fifoLockInv
        iexists slice.slice sl GoInterface (W64 1) sl.len, subslice (sint.nat (W64 1)) (sint.nat sl.len) js,
          items, RunSt.idle, L, b, cf, sc, fn + W64 1
        simp only [named]
        iframe
        isplitl []
        · ipureintro
          refine ⟨?_, Hchain⟩
          simp only [pendOk, subslice]
          rw [← Hd]
          have : sint.nat sl.len = js.length := by word
          rw [this, List.take_of_length_le (by simp)]
          rfl
        iunfold batonAt
        iunfold baton
        iexists ps, Post
        iframe
        iframe #
        ipureintro
        rw [Hb]; exact HLps
      (try wp_auto)
      wp_apply wp_recoverPanic $$ Hpnc as Hpnc
      (try wp_auto)
      iapply HΦ
      iframe
    · iexfalso; iexact Hfrs


end proof

end EtcdGrove
end Perennial
