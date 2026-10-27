/-
`(*fifo).run`, the scheduler's worker. Lean-first (2026-10-22, the scheduler translated with its
body).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.schedule.fifo__run
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

/-- The baton handed to a tracked job: the proposition saved at its `prev`, which is its
`Prev`. -/
theorem baton_prev (p : GName) (Q Prev : IProp GF) :
    ⊢ savedProp p Q -∗ Q -∗ savedProp p Prev -∗ £ 1 -∗ |={⊤}=> Prev := by
  iintro #HQ HQv #HPrev Hlc
  iunfold savedProp at HQ HPrev
  ihave Heq := saved_prop_agree p DFrac.discard DFrac.discard Q Prev $$ HQ HPrev
  ihave Hl : ▷ Prev $$ [Heq HQv]
  · inext
    ihave Hiff := internalEq_iff _ _ $$ Heq
    icases Hiff with ⟨H1, -⟩
    iapply H1
    iexact HQv
  iapply lc_fupd_elim_later $$ Hlc Hl

theorem schedule.fifo.run.wp_proof
    (wp_executeJob : schedule.fifo.executeJob.spec (GF := GF) (hG := hG)) :
    schedule.fifo.run.spec (GF := GF) (hG := hG) := by
  intro l γ F
  wp_start as ⟨#Hf, Hw⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hf' := Hf
  iunfold fifoIs at Hf'
  iNamed Hf'
  iunfold workerRes at Hw
  icases Hw with ⟨Hrun, Hrs, Hrc, Hdc, Hdr⟩
  wp_apply wp_with_defer as %defer Hdefer
  (try wp_auto)
  ihave HI : (("Hrun" ∷ schedRunning γ ∗
      "Hws" ∷ dghostVar F.w (DFrac.own (1 : Qp).half) RunSt.idle ∗
      "Hrc" ∷ dghostVar F.rc (DFrac.own 1) () ∗ "Hdc" ∷ dghostVar F.dc (DFrac.own 1) () ∗
      "Hdr" ∷ dghostVar F.dr (DFrac.own 1) () ∗ "f" ∷ f_ptr ↦ l) : IProp GF)
    $$ [Hrun Hrs Hrc Hdc Hdr f]
  · iframe
  wp_for HI
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlk, HL⟩
  iunfold fifoLockInv at HL
  iNamed HL
  ihave %Hrr := dghostVar_agree F.w _ _ _ _ $$ Hrs Hws
  subst Hrr
  obtain ⟨Hpend, Hchain⟩ := Hjs
  simp only [pendOk] at Hpend
  subst Hpend
  ihave %Hlen := ownSlice_len $$ Hsl
  (try wp_auto)
  wp_if_destruct
  · -- no pending job: the lock released as it was, then `f.resume` or the context's `Done`
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hpend Hsl Hcap Hsch Hfin Hcf Hrs Hq Hitems Hbaton Hst]
    · inext
      iunfold fifoLockInv
      iexists sl, items.map JobItem.j, items, RunSt.idle, L, b, cf, sc, fn
      simp only [named]
      iframe
      ipureintro
      exact ⟨rfl, Hchain⟩
    (try wp_auto)
    ihave #Hctx2 := Hisctx
    iunfold _root_.Perennial.context.isContext at Hctx2
    iunfold _root_.Perennial.context.isContextDef at Hctx2
    icases Hctx2 with ⟨-, #HDoneC, -⟩
    wp_apply +noauto HDoneC as %ch1 %γ1 #Hdone1
    (try wp_auto)
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `<-f.resume`: the next round
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, F.rch, F.γr
      isplit
      · ipureintro; rfl
      isplit
      · iexact Hrch
      unfold recvAu
      clear Hchain Hlen
      iinv Hrinv with Hi Hclose
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hmask
      inext
      iunfold resumeInv at Hi
      icases Hi with ⟨%bl, (Hch | ⟨Hch, Hrc', -⟩)⟩
      · cases bl with
        | nil =>
          iexists .Buffered []
          iframe Hch
        | cons x rest =>
          iexists .Buffered (x :: rest)
          iframe Hch
          dsimp only
          iintro Hch
          imod Hmask with -
          imod Hclose $$ [Hch] with -
          · inext; iunfold resumeInv; iexists rest; ileft; iexact Hch
          imodintro
          (try wp_auto)
          wp_for_post
          simp only [named]
          iframe
      · ihave %Hv := dghostVar_valid_2 F.rc () (DFrac.own 1) () (DFrac.own 1) $$ Hrc Hrc'
        exact absurd Hv.1 (dfrac_own_one_op_invalid _)
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- `<-f.ctx.Done()`: stopped; the pending jobs taken and run with the cancelled context
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch1, γ1
      isplit
      · ipureintro; rfl
      isplit
      · iapply _root_.Perennial.context.isContextDone_is_chan $$ Hdone1
      iapply _root_.Perennial.context.isContextDone_receive _ _ _ _ $$ Hdone1
      iintro ⟨#HPD, -⟩
      simp only [fifoCtxDesc]
      (try wp_auto)
      wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlk, HL⟩
      iunfold fifoLockInv at HL
      iNamed HL
      ihave %Hrr := dghostVar_agree F.w _ _ _ _ $$ Hrs Hws
      subst Hrr
      obtain ⟨Hpend, Hchain⟩ := Hjs
      simp only [pendOk] at Hpend
      subst Hpend
      icases Hst with (⟨%Hcf, Hst⟩ | ⟨%Hcf, -, Htok, Hq'⟩)
      · iunfold stopped at HPD
        ihave %Hv := dghostVar_valid_2 F.st _ _ _ _ $$ Hst HPD
        exact absurd Hv.1 (dfrac_own_one_op_invalid _)
      (try wp_auto)
      imod dghostVar_update_halves RunSt.drained F.w _ _ $$ Hrs Hws with ⟨Hrs, Hws⟩
      have HLpos : 0 < L.length := by have := Hchain.1; omega
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hpend Hsch Hfin Hcf Hrs Hq Hdr Htok Hq']
      · inext
        iunfold fifoLockInv
        iexists slice.nil, [], [], RunSt.drained, L, L.length - 1, cf, sc, fn
        simp only [named]
        iframe
        isplitl []
        · iapply ownSlice_nil
        isplitl []
        · iapply ownSliceCap_nil
        isplitl []
        · ipureintro; exact ⟨rfl, chainOk_nil HLpos⟩
        isplitl []
        · iapply BigSepL.bigSepL_nil.2; itrivial
        isplitl [Hdr]
        · iunfold batonAt; iexact Hdr
        iright
        iframe
        iframe #
        ipureintro; exact Hcf
      (try wp_auto)
      iunfold batonAt at Hbaton
      ihave %Hlen2 := ownSlice_len $$ Hsl
      ihave HR : ((∃ (i : w64) (tv : GoInterface) (b' : Nat),
          "i" ∷ i_ptr ↦ i ∗ "todo" ∷ todo_ptr ↦ tv ∗
          "Hsl" ∷ sl ↦* items.map JobItem.j ∗
          "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sl.len ∧
            chainOk L b' (items.drop (sint.nat i))⌝ ∗
          "Hitems" ∷ ([∗list] it ∈ items.drop (sint.nat i), itemOk γ it) ∗
          "Hbaton" ∷ baton L b' ∗
          "Hrun" ∷ schedRunning γ ∗ "f" ∷ f_ptr ↦ l) : IProp GF)
        $$ [i todo Hsl Hitems Hbaton Hrun f]
      · iexists W64 0, _, b
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        simp only [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
        exact Hchain
      wp_for HR
      wp_if_destruct
      · -- `todo := pendings[i]`, run with the cancelled context
        obtain ⟨Hi0, Hil, Hich⟩ := Hi
        have Hlt : sint.nat i < items.length := by
          have := Hlen2.1; simp only [List.length_map] at this; word
        have Hdrop : items.drop (sint.nat i) = items[sint.nat i] :: items.drop (sint.nat i + 1) :=
          List.drop_eq_getElem_cons Hlt
        rw [Hdrop] at Hich ⊢
        icases BigSepL.bigSepL_cons.1 $$ Hitems with ⟨Hit, Hitems⟩
        (try wp_auto)
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi0, Hif⟩)]
        wp_apply +noauto wp_load_slice_index sl (sint.Z i) (items.map JobItem.j) (DFrac.own 1)
          items[sint.nat i].j Hi0 $$ [Hsl] as Hsl
        · iframe; ipureintro; simp [Hlt]
        wp_auto_lc 1
        iunfold itemOk at Hit
        icases Hit with ⟨#Hjob, HPre, Htr⟩
        have Hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
        rcases Htrk : items[sint.nat i].tr with _ | ⟨pv, ps⟩
        · -- untracked: the baton stays
          icases Htr with %HPP
          obtain ⟨hPrev, hPost⟩ := HPP
          wp_apply wp_executeJob l γ F items[sint.nat i].j items[sint.nat i].Pre
            items[sint.nat i].Prev items[sint.nat i].Post true $$ [Hrun HPre] as ⟨Hrun, -⟩
          · iframe; iframe #
            simp only [↓reduceIte, hPrev]
            iframe
            try (isplitl [] <;> itrivial)
          (try wp_auto)
          wp_for_post
          iframe
          iexists i + W64 1, items[sint.nat i].j, b'
          simp only [named]
          rw [Hi1]
          iframe
          ipureintro
          exact ⟨by word, by word, chainOk_cons_untracked Hich Htrk⟩
        · -- tracked: the baton is its `Prev`, its `Post` the next baton
          icases Htr with ⟨#Hpv, #Hps⟩
          obtain ⟨HLpv, HLps, Hich'⟩ := chainOk_cons_tracked Hich Htrk
          iunfold baton at Hbaton
          icases Hbaton with ⟨%p, %Q, %Hp, #HQs, HQ⟩
          have hp : p = pv := by rw [HLpv] at Hp; exact (Option.some.inj Hp).symm
          subst hp
          imod baton_prev p Q _ $$ HQs HQ Hpv Hlc1 with HPrev
          wp_apply wp_executeJob l γ F items[sint.nat i].j items[sint.nat i].Pre
            items[sint.nat i].Prev items[sint.nat i].Post true $$ [Hrun HPre HPrev]
            as ⟨Hrun, HPost⟩
          · iframe; iframe #
            simp only [↓reduceIte]
            iframe
            itrivial
          (try wp_auto)
          wp_for_post
          iframe
          iexists i + W64 1, items[sint.nat i].j, b' + 1
          simp only [named]
          rw [Hi1]
          iframe
          isplitr [HPost]
          · ipureintro; exact ⟨by word, by word, Hich'⟩
          iunfold baton
          iexists ps, items[sint.nat i].Post
          iframe
          iframe #
          ipureintro; exact HLps
      · -- the jobs run: `return`, `f.donec` and `f.resume` closed
        (try wp_auto)
        wp_for_post
        (try wp_auto)
        clear Hi Hchain Hlen Hlen2
        wp_bind (App (Val #(functions go.close _)) _)
        wp_apply_core chan.wp_close (V := Unit) F.dch F.γd $$ Hdch
        iintro -
        unfold closeAu
        iinv Hdinv with Hdi Hclose
        iapply fupd_mask_intro Std.LawfulSet.empty_subset
        iintro Hmask
        inext
        iunfold donecInv at Hdi
        icases Hdi with (Hch | ⟨Hch, Hdc'⟩)
        rotate_left
        · ihave %Hv := dghostVar_valid_2 F.dc () (DFrac.own 1) () (DFrac.own 1) $$ Hdc Hdc'
          exact absurd Hv.1 (dfrac_own_one_op_invalid _)
        iexists .Buffered []
        iframe Hch
        dsimp only
        iintro Hch
        imod Hmask with -
        imod Hclose $$ [Hch Hdc] with -
        · inext; iunfold donecInv; iright; iframe
        imodintro
        (try wp_auto)
        wp_bind (App (Val #(functions go.close _)) _)
        wp_apply_core chan.wp_close (V := Unit) F.rch F.γr $$ Hrch
        iintro -
        unfold closeAu
        clear Hif Hcf HLpos Hcfnn
        iinv Hrinv with Hri Hclose
        iapply fupd_mask_intro Std.LawfulSet.empty_subset
        iintro Hmask
        inext
        iunfold resumeInv at Hri
        icases Hri with ⟨%bl, (Hch | ⟨Hch, Hrc', -⟩)⟩
        rotate_left
        · ihave %Hv := dghostVar_valid_2 F.rc () (DFrac.own 1) () (DFrac.own 1) $$ Hrc Hrc'
          exact absurd Hv.1 (dfrac_own_one_op_invalid _)
        iexists .Buffered bl
        iframe Hch
        dsimp only
        iintro Hch
        imod Hmask with -
        imod Hclose $$ [Hch Hrc] with -
        · inext; iunfold resumeInv; iexists bl; iright; iframe; iframe #
        imodintro
        (try wp_auto)
        iunfold schedRunning at Hrun
        icases Hrun with ⟨-, Htok⟩
        iapply HΦ $$ Htok

    iapply BigAndL.bigAndL_nil.2
    itrivial
  · -- a pending job: the head taken, run outside the lock
    cases items with
    | nil => simp at Hlen; exact absurd (by word) Hif
    | cons it its =>
    simp only [List.map_cons] at Hlen ⊢
    (try wp_auto)
    have hpos : 0 < sint.Z sl.len := by
      obtain ⟨h1, h2⟩ := Hlen; simp only [List.length_cons] at h1; word
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, hpos⟩)]
    wp_apply +noauto wp_load_slice_index sl (sint.Z (W64 0)) (it.j :: its.map JobItem.j)
      (DFrac.own 1) it.j (by decide) $$ [Hsl] as Hsl
    · iframe; ipureintro; rfl
    wp_auto_lc 1
    icases BigSepL.bigSepL_cons.1 $$ Hitems with ⟨Hit, Hitems⟩
    iunfold itemOk at Hit
    icases Hit with ⟨#Hjob, HPre, Htr⟩
    ihave #Hjob' := Hjob
    iunfold jobIs at Hjob'
    icases Hjob' with ⟨%jt, %Hj, -⟩
    rcases Htrk : it.tr with _ | ⟨pv, ps⟩
    · -- untracked: the baton stays in the invariant
      icases Htr with %HPP
      obtain ⟨hPrev, hPost⟩ := HPP
      imod dghostVar_update_halves RunSt.runU F.w _ _ $$ Hrs Hws with ⟨Hrs, Hws⟩
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hpend Hsl Hcap Hsch Hfin Hcf Hrs Hq Hitems Hbaton
        Hst]
      · inext
        iunfold fifoLockInv
        iexists sl, it.j :: its.map JobItem.j, its, RunSt.runU, L, b, cf, sc + W64 1, fn
        simp only [named]
        iframe
        isplitl []
        · ipureintro
          exact ⟨⟨by simp, by simp⟩, chainOk_cons_untracked Hchain Htrk⟩
        iunfold batonAt at Hbaton
        iunfold batonAt
        iexact Hbaton
      (try wp_auto)
      rw [Hj]
      (try wp_auto)
      rw [← Hj]
      wp_apply wp_executeJob l γ F it.j it.Pre it.Prev it.Post false $$ [Hrun HPre Hws]
        as ⟨Hrun, Hws⟩
      · iframe; iframe #
        simp only [Bool.false_eq_true, ↓reduceIte, hPrev]
        isplitl []
        · itrivial
        iunfold finishPre
        iexists RunSt.runU
        iframe
        ipureintro; exact hPost
      (try wp_auto)
      wp_for_post
      simp only [named]
      iframe
    · -- tracked: the baton is its `Prev`; its `Post` comes back as the baton at `b + 1`
      icases Htr with ⟨#Hpv, #Hps⟩
      obtain ⟨HLpv, HLps, Hch'⟩ := chainOk_cons_tracked Hchain Htrk
      iunfold batonAt at Hbaton
      iunfold baton at Hbaton
      icases Hbaton with ⟨%p, %Q, %Hp, #HQs, HQ⟩
      have hp : p = pv := by rw [HLpv] at Hp; exact (Option.some.inj Hp).symm
      subst hp
      imod baton_prev p Q _ $$ HQs HQ Hpv Hlc1 with HPrev
      ihave #Hlb := monoListLbOwn_get γ.jobs _ L $$ Hq
      ihave #Hidx := monoListIdxOwn_get (b + 1) ps HLps $$ Hlb
      imod dghostVar_update_halves (RunSt.runT b) F.w _ _ $$ Hrs Hws with ⟨Hrs, Hws⟩
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hpend Hsl Hcap Hsch Hfin Hcf Hrs Hq Hitems Hst]
      · inext
        iunfold fifoLockInv
        iexists sl, it.j :: its.map JobItem.j, its, RunSt.runT b, L, b + 1, cf, sc + W64 1, fn
        simp only [named]
        iframe
        isplitl []
        · ipureintro
          exact ⟨⟨by simp, by simp⟩, Hch'⟩
        iunfold batonAt
        ipureintro; rfl
      (try wp_auto)
      rw [Hj]
      (try wp_auto)
      rw [← Hj]
      wp_apply wp_executeJob l γ F it.j it.Pre it.Prev it.Post false $$ [Hrun HPre HPrev Hws]
        as ⟨Hrun, Hws⟩
      · iframe; iframe #
        simp only [Bool.false_eq_true, ↓reduceIte]
        iunfold finishPre
        iexists RunSt.runT b
        iframe
        iexists ps
        iframe #
      (try wp_auto)
      wp_for_post
      simp only [named]
      iframe

end proof

end EtcdGrove
end Perennial
