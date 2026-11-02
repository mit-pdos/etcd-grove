/- Lean-first (no Rocq counterpart). The proof of `db.Commit(v)`'s crash-aware spec: as
`DB__Commit.lean`'s, over `isDBC` (`rwRC`, `metaRC`), with `DB.commit.specCrash`, whose `bootOk`
premise comes from `isDBC`'s `vpBoot`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__CommitCrash
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__commitCrash
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__Commit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

/-- `rwRC`'s open branch, from the writer's part. -/
theorem rwRC_of_writerStC (γ : DBNames) (γc : GName) (db f : Loc) (fd : w64) (p : GoString)
    (mp : List w8) (fl : Bool) (hwm : Nat) (st : MapSt) (m : OsMeta) (bs : List (w8 × Bool))
    (hok : fl = false → m.ok = true) :
    writerStC (GF := GF) γ γc db f fd p mp fl hwm st m bs ∗
      (match st with | none => dbFailed (GF := GF) γ | some _ => emp) ⊢
      rwRC (GF := GF) γ γc db f fd p := by
  unfold writerStC rwRC
  iintro ⟨⟨Hcur, Hmap, Hout, Hflds, Hw, Hcls, Hst⟩, Hf⟩
  ileft
  iexists mp, fl, hwm, st, m, bs
  iframe
  isplitr
  · ipureintro; exact hok
  rcases st with _ | ⟨base, len, γm⟩
  · dsimp only; iframe
  · dsimp only; iexact Hst

/-- Failing the handle under `metalock`, after a failed `commit`: `metaRC` failed, `rwRC`, and the
committer's token at high water mark 0. -/
theorem fail_handleC (γ : DBNames) (γc : GName) (db f : Loc) (fd : w64) (p : GoString) (t n : Nat)
    (mp' : List w8) (fl : Bool) (hwm : Nat) (st : MapSt) (m : OsMeta) (bs : List (w8 × Bool)) :
    dbOwner (GF := GF) γ t n ∗ writerStFC (GF := GF) γ γc db f fd p mp' fl hwm st m bs ∗
      (⌜fl = false⌝ ∨ (⌜fl = true⌝ ∗ dbFailed (GF := GF) γ)) ∗ metaRC (GF := GF) γ db p ⊢
      |={⊤}=> ∃ b : Bool, db.[DB, go!"failed"] ↦ b ∗
        (db.[DB, go!"failed"] ↦ true -∗ metaRC (GF := GF) γ db p ∗ rwRC (GF := GF) γ γc db f fd p ∗
          dbFailed (GF := GF) γ ∗ dbOwner (GF := GF) γ t 0) := by
  iintro ⟨Hown, Hws, Hfl, HM⟩
  iunfold dbOwner at Hown
  iunfold metaRC at HM
  icases HM with ⟨%b, %mp, %hwm0, %c, %T, Hfa, Hcur, Hmb, Hauth, Hout, Hrest⟩
  unfold writerStFC
  icases Hws with ⟨Hcur1, Hmap1, Hout1, Hflds1, Hw, Hcls1, Hst⟩
  icombine Hcur1 Hcur gives % ⟨_, Heq⟩
  cases Heq
  cases fl with
  | true =>
    icases Hfl with (%Hbad | ⟨-, #Hfailed⟩)
    · cases Hbad
    icases Hrest with ⟨Hfa0, %t3, Hown3⟩
    icombine Hown Hown3 gives % ⟨_, Heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj Heq
    imodintro
    iexists true
    iframe Hfa
    iintro Hfa
    isplitl [Hfa Hcur Hmb Hauth Hout Hfa0 Hown3]
    · iunfold metaRC
      iexists true, mp', hwm, c, T
      iframe Hfa Hcur Hmb Hauth Hout
      dsimp only
      iframe Hfa0
      iexists t; iexact Hown3
    unfold dbOwner; iframe Hown
    isplitl
    · iapply rwRC_of_writerStC γ γc db f fd p mp' true hwm st m bs (fun h => by cases h)
      unfold writerStC
      rcases st with _ | ⟨base, len, γm⟩ <;> dsimp only <;> iframe <;> iframe #
    · iexact Hfailed
  | false =>
    iclear Hfl
    icases Hrest with ⟨Hfail, -, -, Hown3, -⟩
    imod ghostVar_update_halves (t, 0) γ.own _ _ $$ Hown Hown3 with ⟨Hown, Hown3⟩
    imod mono_nat_own_update 1 (by omega) $$ Hfail with ⟨Hfail, #Hfailed⟩
    rcases st with _ | ⟨base, len, γm⟩
    · dsimp only
      iunfold writerExtra at Hst
      icases Hst with ⟨Hcurx, Hf2, Hfd2⟩
      imod fail_cur γ mp' hwm $$ [Hcur1 Hcurx Hcur] with ⟨Hcur1, Hcurx, Hcur⟩
      · iframe
      imodintro
      iexists false
      iframe Hfa
      iintro Hfa
      isplitl [Hfa Hcur Hmb Hauth Hout Hfail Hown3]
      · iunfold metaRC
        iexists true, mp', hwm, c, T
        iframe
        dsimp only; iframe Hfail; iexists t; iexact Hown3
      unfold dbOwner; iframe Hown
      isplitl
      · iapply rwRC_of_writerStC γ γc db f fd p mp' true hwm none m bs (fun h => by cases h)
        unfold writerStC
        dsimp only
        iframe Hcur1 Hmap1 Hout1 Hflds1 Hw Hcls1
        isplitl
        · iunfold writerExtra; iframe
        · unfold dbFailed; iexact Hfailed
      · unfold dbFailed; iexact Hfailed
    · dsimp only
      icases Hst with ⟨%Hst, Htok1, #Hinv, Hwc⟩
      imod fail_cur_inv γ p base len γm mp' hwm $$ [Hinv Htok1 Hcur1 Hcur] with ⟨Htok1, Hcur1, Hcur⟩
      · iframe; iframe #
      imodintro
      iexists false
      iframe Hfa
      iintro Hfa
      isplitl [Hfa Hcur Hmb Hauth Hout Hfail Hown3]
      · iunfold metaRC
        iexists true, mp', hwm, c, T
        iframe
        dsimp only; iframe Hfail; iexists t; iexact Hown3
      unfold dbOwner; iframe Hown
      isplitl
      · iapply rwRC_of_writerStC γ γc db f fd p mp' true hwm (some (base, len, γm)) m bs
          (fun h => by cases h)
        unfold writerStC
        dsimp only
        iframe Hcur1 Hmap1 Hout1 Hflds1 Hw Hcls1 Htok1 Hwc; iframe #; ipureintro; exact Hst
      · unfold dbFailed; iexact Hfailed

theorem DB.Commit.wp_proof_crash (wp_meta : DB.«meta».spec (GF := GF) (hG := hG))
    (wp_commit : DB.commit.specCrash (GF := GF) (hG := hG)) :
    DB.Commit.specCrash (GF := GF) (hG := hG) := by
  intro γ γc db t n v Ht Hvp
  wp_start as ⟨Hdb, Hown⟩
  iunfold isDBC at Hdb
  icases Hdb with ⟨⟨%f, %fd, %p, #Hpkg, #Hos, #Hfile, #Hpath, #Hci, #Hrw, #Hmeta, #Hguard⟩, %hboot, -⟩
  ihave #Hpkg2 := Hpkg
  iunfold pkgFacts at Hpkg2
  icases Hpkg2 with ⟨#Hsync, %e1, %e2, #He1, -, %He, -⟩
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock db.[DB, go!"rwlock"] (rwRC (GF := GF) γ γc db f fd p) $$ [$Hrw $Hsync]
    as ⟨Hl1, HW⟩
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock db.[DB, go!"metalock"] (metaRC (GF := GF) γ db p) $$ [$Hmeta $Hsync]
    as ⟨Hl2, HM⟩
  (try wp_auto)
  iunfold metaRC at HM
  icases HM with ⟨%b, %mx, %hwm, %c, %T, Hfl, Hcur, Hmb, Hauth, Hout, Hrest⟩
  iunfold dbOwner at Hown
  iunfold rwRC at HW
  icases HW with (⟨%mp1, %fl, %hwm1, %st, %m, %bs, Hcur1, Hmap1, Hout1, Hflds1, Hw, Hcls1, %Hmok, Hst⟩ |
    ⟨⟨%x, Hown2⟩, Hcls1, %st, Hmap1, Hflds1⟩)
  rotate_left
  · -- closed: three halves of `own`
    iexfalso
    cases b with
    | true =>
      icases Hrest with ⟨-, %x3, Hown3⟩
      iapply ghostVar_halves3 γ.own (t, n) x _; iframe
    | false =>
      icases Hrest with ⟨-, -, -, Hown3, -⟩
      iapply ghostVar_halves3 γ.own (t, n) x _; iframe
  cases b with
  | true =>
    icases Hrest with ⟨Hfa, %t3, Hrest⟩
    icombine Hown Hrest gives % ⟨_, Heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj Heq
    ihave #Hfailed := monoNatLbOwn_get γ.fail 1 1 $$ Hfa
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock db.[DB, go!"metalock"] (metaRC (GF := GF) γ db p)
      $$ [$Hmeta $Hsync $Hl2 Hfl Hcur Hmb Hauth Hout Hfa Hrest]
    · iunfold metaRC
      iexists true, mx, hwm, c, T
      iframe Hfl Hcur Hmb Hauth Hout
      dsimp only; iframe Hfa; iexists t; iexact Hrest
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock db.[DB, go!"rwlock"] (rwRC (GF := GF) γ γc db f fd p)
      $$ [$Hrw $Hsync $Hl1 Hcur1 Hmap1 Hout1 Hflds1 Hw Hcls1 Hst]
    · iunfold rwRC; ileft
      iexists mp1, fl, hwm1, st, m, bs
      iframe
      ipureintro; exact Hmok
    (try wp_auto)
    iapply HΦ
    iright
    iframe
    isplitr
    · ipureintro; exact He.1
    unfold dbFailed dbOwner; iframe; iframe #
  | false =>
    icases Hrest with ⟨Hfa, %Hok, Hlast, Hown3, %B, #HB, #Htx, %HT⟩
    obtain ⟨Hok, rfl, HTn⟩ := Hok
    icombine Hown Hown3 gives % ⟨_, Heq⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj Heq
    icombine Hcur Hcur1 gives % ⟨_, Heq⟩
    cases Heq
    rcases st with _ | ⟨base, len, γm⟩
    · dsimp only
      icases Hst with ⟨Hfailed, -⟩
      iexfalso
      iunfold dbFailed at Hfailed
      icases monoNatLbOwn_valid γ.fail 1 0 1 $$ Hfa Hfailed with %Hbad
      omega
    dsimp only
    icases Hst with ⟨%Hst, Htok1, #Hinv, Hwc⟩
    (try wp_auto)
    imod metas_out γ p base len γm mx (curPgid mx) $$ [Hinv Htok1 Hcur1 Hout1 Hout]
      with ⟨Htok1, Hcur1, Hout1, Hout, Hc0, Hc1⟩
    · iframe; iframe #
    have hl : mx.length = 8192 := Hok.1
    have hb16 : 0 < (base +ₗ ((16 : Nat) : Int)).addr := by simp only [Loc.add]; omega
    have hb4112 : 0 < (base +ₗ ((4112 : Nat) : Int)).addr := by simp only [Loc.add]; omega
    icases (cellsB_meta base 16 _ (by simp; omega) hb16).1 $$ Hc0 with Hm0
    icases (cellsB_meta base 4112 _ (by simp; omega) hb4112).1 $$ Hc1 with Hm1
    rw [← fileMeta_cells0, ← fileMeta_cells1]
    dsimp only [mapFields]
    icases Hflds1 with ⟨Hd, H0, H1⟩
    have hn0 : (base +ₗ ((16 : Nat) : Int)) ≠ null := by
      intro h; rw [h] at hb16; simp [null] at hb16
    have hn1 : (base +ₗ ((4112 : Nat) : Int)) ≠ null := by
      intro h; rw [h] at hb4112; simp [null] at hb4112
    wp_apply wp_meta db (base +ₗ ((16 : Nat) : Int)) (base +ₗ ((4112 : Nat) : Int)) (fileMeta mx 0)
        (fileMeta mx 1) _ _ _ Hok.2.1 $$ [H0 H1 Hm0 Hm1] as ⟨H0, H1, Hm0, Hm1⟩
    · iframe; ipureintro; exact ⟨hb16, hb4112⟩
    ihave Hpick : (pickMetaRes (base +ₗ ((16 : Nat) : Int)) (fileMeta mx 0) (base +ₗ ((4112 : Nat) : Int))
        (fileMeta mx 1)) ↦{DFrac.own (1 : Qp).half} curMeta mx ∗
      ((pickMetaRes (base +ₗ ((16 : Nat) : Int)) (fileMeta mx 0) (base +ₗ ((4112 : Nat) : Int))
        (fileMeta mx 1)) ↦{DFrac.own (1 : Qp).half} curMeta mx -∗
        (base +ₗ ((16 : Nat) : Int)) ↦{DFrac.own (1 : Qp).half} fileMeta mx 0 ∗
        (base +ₗ ((4112 : Nat) : Int)) ↦{DFrac.own (1 : Qp).half} fileMeta mx 1) $$ [Hm0 Hm1]
    · rcases pick_cur mx _ _ Hok.2.1 hn0 hn1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;>
        iframe <;> iintro H <;> iframe
    icases Hpick with ⟨Hpm, Hback⟩
    (try wp_auto)
    icases Hback $$ Hpm with ⟨Hm0, Hm1⟩
    rw [fileMeta_cells0, fileMeta_cells1]
    icases (cellsB_meta base 16 _ (by simp; omega) hb16).2 $$ Hm0 with Hc0
    icases (cellsB_meta base 4112 _ (by simp; omega) hb4112).2 $$ Hm1 with Hc1
    have hl1 : ((mx.drop 16).take 64).length = 64 := by simp; omega
    have e1 : ((mx.drop 16).take 64 ++ (mx.drop 4112).take 64).take 64 = (mx.drop 16).take 64 :=
      List.take_left' hl1
    have e2 : ((mx.drop 16).take 64 ++ (mx.drop 4112).take 64).drop 64 = (mx.drop 4112).take 64 :=
      List.drop_left' hl1
    have hmc128 : ((mx.drop 16).take 64 ++ (mx.drop 4112).take 64).length = 128 := by
      rw [List.length_append, hl1]
      have : ((mx.drop 4112).take 64).length = 64 := by simp; omega
      rw [this]
    imod metas_in γ p base len γm mx false (curPgid mx)
        ((mx.drop 16).take 64 ++ (mx.drop 4112).take 64) hmc128 (fun _ => rfl)
        $$ [Htok1 Hcur1 Hout1 Hout Hc0 Hc1] with ⟨Htok1, Hcur1, Hout1, Hout⟩
    · rw [e1, e2]; iframe; iframe #
    wp_apply sync.Mutex.wp_Unlock db.[DB, go!"metalock"] (metaRC (GF := GF) γ db p)
      $$ [$Hmeta $Hsync $Hl2 Hfl Hcur Hmb Hauth Hout Hfa Hlast Hown3]
    · iunfold metaRC
      iexists false, mx, curPgid mx, c, T
      iframe
      dsimp only
      iframe
      isplitr
      · ipureintro; exact ⟨Hok, rfl, HTn⟩
      iframe
      iexists B; iframe #; ipureintro; exact HT
    (try wp_auto)
    wp_apply wp_commit γ γc db f fd p mx (some (base, len, γm)) m bs v Hok Ht (Hmok rfl) (by simp) Hvp
        (hboot _ _ Hvp)
      $$ [Hown Hcur1 Hmap1 Hout1 Hd H0 H1 Hw Hcls1 Htok1 Hwc] as %err Hr
    · iframe #
      unfold writerStC dbOwner
      dsimp only [mapFields]
      iframe; iframe #
      ipureintro; exact Hst
    icases Hr with (⟨%Herr, HW, Hown, #Htx', #Hlast'⟩ |
      ⟨%Herr, ⟨%n', Hown⟩, %mp', %fl', %hwm', %st', %m', %bs', Hws, Hfl'⟩)
    · subst Herr
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock db.[DB, go!"rwlock"] (rwRC (GF := GF) γ γc db f fd p)
        $$ [$Hrw $Hsync $Hl1 HW]
      · iexact HW
      (try wp_auto)
      iapply HΦ
      ileft
      iframe; iframe #
      ipureintro; rfl
    · cases err with
      | nil => exact absurd rfl Herr
      | ok ie =>
      (try wp_auto)
      wp_apply sync.Mutex.wp_Lock db.[DB, go!"metalock"] (metaRC (GF := GF) γ db p) $$ [$Hmeta $Hsync]
        as ⟨Hl2, HM⟩
      imod fail_handleC γ γc db f fd p _ _ mp' fl' hwm' st' m' bs' $$ [Hown Hws Hfl' HM] with ⟨%b, Hf, Hk⟩
      · iframe
      (try wp_auto)
      icases Hk $$ Hf with ⟨HM, HW, #Hfailed, Hown⟩
      wp_apply sync.Mutex.wp_Unlock db.[DB, go!"metalock"] (metaRC (GF := GF) γ db p)
        $$ [$Hmeta $Hsync $Hl2 HM]
      · iexact HM
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock db.[DB, go!"rwlock"] (rwRC (GF := GF) γ γc db f fd p)
        $$ [$Hrw $Hsync $Hl1 HW]
      · iexact HW
      (try wp_auto)
      iapply HΦ
      iright
      iframe; iframe #
      ipureintro; exact Herr

end proof

end bboltfs
end EtcdGrove
end Perennial
