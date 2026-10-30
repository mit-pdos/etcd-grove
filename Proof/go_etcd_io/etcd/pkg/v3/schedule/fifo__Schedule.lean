/-
`(*fifo).Schedule`. Lean-first (2026-10-22, the scheduler translated with its body).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.schedule.fifo__Schedule
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

/-- A `Schedule` after `Stop` is excluded: a tracked one brings a half of the queue beyond the
lock invariant's half and fraction `q`, an untracked one `schedLive`, which the stop token
excludes. -/
theorem schedPre_stopped (γ : SchedNames) (tr : Option (List GName × GName × GName))
    (Prev Post : IProp GF) (L : List GName) (q : Qp) :
    ⊢ schedPre γ tr Prev Post -∗ schedStopTok γ -∗ monoListAuthOwn γ.jobs (1 : Qp).half L -∗
      monoListAuthOwn γ.jobs q L -∗ False := by
  iintro Hpre Htok Hq1 Hq2
  cases tr with
  | none =>
    simp only [schedPre]
    icases Hpre with ⟨-, Hlive⟩
    iunfold schedLive at Hlive
    iunfold schedStopTok at Htok
    icases Hlive with ⟨%n, #Hn, #Hd⟩
    icases Htok with ⟨%n', #Hn', Hd'⟩
    iunfold schedStopName at Hn Hn'
    ihave %Hnn := mono_list_idx_agree γ.jobs 0 n n' $$ Hn Hn'
    subst Hnn
    ihave %Hv := dghostVar_valid_2 n () (DFrac.own 1) () DFrac.discard $$ Hd' Hd
    exact absurd Hv.1 (dfrac_own_one_op_invalid _)
  | some x =>
    obtain ⟨Ps, prev, post⟩ := x
    simp only [schedPre]
    icases Hpre with ⟨Hq, -, -⟩
    iunfold schedQueue at Hq
    ihave Hq12 := (monoListAuthOwn_fractional γ.jobs L).fractional (1 : Qp).half q
      |>.2 $$ [Hq1 Hq2]
    · iframe
    ihave %Hv := monoListAuthOwn_agree γ.jobs _ _ _ _ $$ Hq12 Hq
    exfalso
    have h' := Qp.le_iff.1 Hv.1
    have hq := q.2
    have hh : ((1 : Qp).half).val = 1 / 2 := rfl
    have h1 : (1 : Qp).val = 1 := rfl
    have hs : (((1 : Qp).half + q) + (1 : Qp).half).val = 1 / 2 + q.val + 1 / 2 := rfl
    rw [hs, h1] at h'
    grind

/-- The baton read in a longer queue. -/
theorem batonAt_app (F : FifoNames) (L L' : List GName) (b : Nat) (rs : RunSt) :
    batonAt (GF := GF) F L b rs ⊢ batonAt F (L ++ L') b rs := by
  rcases rs with _ | _ | k | _ <;> simp only [batonAt] <;> try (iintro H; iexact H)
  all_goals
    iintro H
    iunfold baton at H
    iunfold baton
    icases H with ⟨%p, %Q, %Hp, #Hs, HQ⟩
    iexists p, Q
    iframe
    iframe #
    ipureintro
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 Hp).1]; exact Hp

theorem schedule.fifo.Schedule.wp_proof : schedule.fifo.Schedule.spec (GF := GF) (hG := hG) := by
  intro l γ F j Pre Prev Post tr
  wp_start as ⟨#Hf, #Hjob, HPre, Htr⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold fifoIs at Hf
  iNamed Hf
  wp_apply wp_with_defer as %defer Hdefer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlk, HI⟩
  iunfold fifoLockInv at HI
  iNamed HI
  (try wp_auto)
  icases Hst with (⟨%Hcf, Hst⟩ | ⟨%Hcf, #Hstp, Htok, Hq'⟩)
  rotate_left
  · iexfalso
    icases Hq' with ⟨%q, Hq'⟩
    iapply schedPre_stopped γ tr Prev Post L q $$ Htr Htok Hq Hq'
  subst Hcf
  simp only [decide_eq_false Hcfnn]
  wp_auto
  -- `if len(f.pendings) == 0 { select { case f.resume <- struct{}{}: default: } }`: a send to the
  -- buffered `f.resume`, open while not stopped (`Hst`), or nothing
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ dghostVar F.st (DFrac.own 1) false ∗
      f_ptr ↦ l)))
    $$ [Hst f]
  · wp_if_destruct
    · (try wp_auto)
      wp_apply_core chan.wp_select_nonblocking
      isplit
      · iapply BigAndL.bigAndL_cons.2
        isplit
        · simp only [chan.nonblockingClausePre]
          iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, F.rch, F.γr, ()
          isplitr
          · ipureintro; exact ⟨rfl, rfl⟩
          isplitr
          · iexact Hrch
          unfold nonblockingSendAu nonblockingSendAuInner
          isplit
          · iinv Hrinv with Hi Hclose
            iapply fupd_mask_intro Std.LawfulSet.empty_subset
            iintro Hmask
            inext
            iunfold resumeInv at Hi
            icases Hi with ⟨%bl, (Hch | ⟨Hch, -, #Hstp⟩)⟩
            · iexists .Buffered bl
              iframe Hch
              dsimp only
              iintro Hch
              imod Hmask with -
              imod Hclose $$ [Hch] with -
              · inext; iunfold resumeInv; iexists bl ++ [()]; ileft; iexact Hch
              imodintro
              wp_auto
              iframe Hst f
              try (ipureintro; rfl)
            · iunfold stopped at Hstp
              ihave %Hv := dghostVar_valid_2 F.st _ _ _ _ $$ Hst Hstp
              exact absurd Hv.1 (dfrac_own_one_op_invalid _)
          · itrivial
        iapply BigAndL.bigAndL_nil.2
        itrivial
      · (try wp_auto)
        iframe Hst f
        try (ipureintro; rfl)
    · (try wp_auto)
      iframe Hst f
      try (ipureintro; rfl)
  iintro %v ⟨%Hv, Hst, f⟩
  subst Hv
  wp_auto
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %jsl ⟨Hjsl, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  wp_apply wp_slice_append $$ [Hsl Hcap Hjsl] as %sl' ⟨Hsl, Hcap, -⟩
  · iframe
  (try wp_auto)
  obtain ⟨Hpend, Hchain⟩ := Hjs
  cases tr with
  | none =>
    simp only [schedPre, schedPost]
    icases Htr with ⟨%HPP, #Hlive⟩
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hpend Hsl Hcap Hsch Hfin Hcf Hrs Hq Hitems Hbaton Hst
      HPre]
    · inext
      iunfold fifoLockInv
      iexists sl', js ++ [j], items ++ [⟨j, Pre, Prev, Post, none⟩], rs, L, b, F.cf, sc, fn
      simp only [named]
      iframe
      isplitr
      · ipureintro
        exact ⟨pendOk_append (it := ⟨j, Pre, Prev, Post, none⟩) Hpend,
          chainOk_append_untracked Hchain rfl⟩
      iapply BigSepL.bigSepL_singleton.2
      iunfold itemOk
      simp only
      iframe
      iframe #
      ipureintro; exact HPP
    iapply HΦ
    itrivial
  | some x =>
    obtain ⟨Ps, prev, post⟩ := x
    simp only [schedPre, schedPost]
    icases Htr with ⟨HqS, #Hprev, #Hpost⟩
    iunfold schedQueue at HqS
    ihave %HL := monoListAuthOwn_agree γ.jobs _ _ _ _ $$ Hq HqS
    obtain ⟨-, rfl⟩ := HL
    ihave Hfull := (monoListAuthOwn_fractional γ.jobs (Ps ++ [prev])).fractional (1 : Qp).half
      (1 : Qp).half |>.2 $$ [Hq HqS]
    · iframe
    rw [Qp.half_add_half] at *
    imod monoListAuthOwn_update_app [post] $$ Hfull with Hfull
    icases Hfull with ⟨Hfull, -⟩
    ihave ⟨Hq, HqS⟩ := (monoListAuthOwn_fractional γ.jobs ((Ps ++ [prev]) ++ [post])).fractional
      (1 : Qp).half (1 : Qp).half |>.1 $$ [Hfull]
    · rw [Qp.half_add_half]; iexact Hfull
    have hL : (Ps ++ [prev]) ++ [post] = Ps ++ [prev, post] := by simp
    rw [hL]
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hpend Hsl Hcap Hsch Hfin Hcf Hrs Hq Hitems Hbaton Hst
      HPre]
    · inext
      iunfold fifoLockInv
      iexists sl', js ++ [j], items ++ [⟨j, Pre, Prev, Post, some (prev, post)⟩], rs,
        Ps ++ [prev, post], b, F.cf, sc, fn
      simp only [named]
      iframe
      isplitr
      · ipureintro
        exact ⟨pendOk_append (it := ⟨j, Pre, Prev, Post, some (prev, post)⟩) Hpend,
          chainOk_append_tracked Hchain rfl⟩
      isplitr [Hbaton]
      · iapply BigSepL.bigSepL_singleton.2
        iunfold itemOk
        simp only
        iframe
        iframe #
      rw [← hL]
      iapply batonAt_app $$ Hbaton
    iapply HΦ
    iunfold schedQueue
    iexact HqS

end proof

end EtcdGrove
end Perennial
