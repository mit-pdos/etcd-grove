/-
The proof of `os.RemoveAll.specSubS` (`Spec/os/RemoveAll.lean`): `RemoveAll(d/b)` of an entry holding
anything, with the whole claims of every directory under it. `model.removeAllFrom` on such an entry
(`wp_removeAllFrom_sub`) by induction on the number of claims: a name holding a file or nothing is
`RemoveAllLeaf.lean`'s; a directory `J` is `RemoveAllFrom.lean`'s passes with each name removed by the
induction hypothesis, on the claims but `J`'s (the pool, `os.rmPool`), which cover each name's subtree
(`subCover_pool`: no directory under `J` is `J`, `ClRanked`). Lean-first; untrusted.
-/
module

public import Proof.os.RemoveAllTop
public import Proof.os.RemoveAllCover

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

theorem os.osClaimsW_append (a b : List Claim) :
    osClaimsW (GF := GF) (a ++ b) ⊣⊢ osClaimsW a ∗ osClaimsW b := by
  unfold osClaimsW; exact BigSepL.bigSepL_append

theorem os.osClaimsW_cons (x : Claim) (a : List Claim) :
    osClaimsW (GF := GF) (x :: a) ⊣⊢ osNames x.1 x.2.1 (DFrac.own 1) x.2.2 ∗ osClaimsW a := by
  unfold osClaimsW; exact BigSepL.bigSepL_cons

/-- A claim taken out of the middle of a list. -/
theorem os.osClaimsW_take (a b : List Claim) (x : Claim) :
    osClaimsW (GF := GF) (a ++ x :: b) ⊢ osClaimsW (a ++ b) ∗ osNames x.1 x.2.1 (DFrac.own 1) x.2.2 := by
  iintro H
  icases (os.osClaimsW_append a _).1 $$ H with ⟨Ha, Hb⟩
  icases (os.osClaimsW_cons x b).1 $$ Hb with ⟨Hx, Hb⟩
  iframe Hx
  iapply (os.osClaimsW_append a b).2
  iframe

/-- A claim put back in the middle of a list. -/
theorem os.osClaimsW_put (a b : List Claim) (x : Claim) :
    osClaimsW (GF := GF) (a ++ b) ∗ osNames x.1 x.2.1 (DFrac.own 1) x.2.2 ⊢ osClaimsW (a ++ x :: b) := by
  iintro ⟨H, Hx⟩
  icases (os.osClaimsW_append a b).1 $$ H with ⟨Ha, Hb⟩
  iapply (os.osClaimsW_append a _).2
  iframe Ha
  iapply (os.osClaimsW_cons x b).2
  iframe

/-- **After the removal of `b` of `j`** (its claim's history `h` before, the claims `cl` of the
directories under it): the claim on `b`, holding what it held or nothing; the claims, holding some of
what they held (`specSubS`'s post). -/
def os.rmSubOut (j : Ino) (b : GoString) (h : NamesH) (cl : List Claim) (G : Prop) : IProp GF :=
  iprop(∃ (h' : NamesH) (cl' : List Claim), osNames j (.only [b]) (DFrac.own 1) h' ∗ osClaimsW cl' ∗
    ⌜EntsSub h'.cur h.cur ∧ ClsSub cl' cl ∧ (G → h'.cur !! b = none)⌝)

/-- **The pool of a directory's removal**: the claims `l1 ++ l2` of the directories under it (but its
own), each holding some of what it held. -/
def os.rmPool (l1 l2 : List Claim) : IProp GF :=
  iprop(∃ pool : List Claim, osClaimsW pool ∗ ⌜ClsSub pool (l1 ++ l2)⌝)

/-- The removal's state of a directory `J` (`rmAllOutP`: its first arm says `P`) and its pool, as
`rmSubOut`, `b` gone when `G` (which excludes `P`). -/
theorem os.rmSubOut_ofP (j : Ino) (b : GoString) (J : Ino) (h hJ0 : NamesH) (l1 l2 : List Claim)
    (P G : Prop) (hG : G → ¬ P) :
    os.rmAllOutP (GF := GF) j b J h hJ0 P ∗ os.rmPool l1 l2 ⊢
      os.rmSubOut j b h (l1 ++ (J, NameSet.except [], hJ0) :: l2) G := by
  unfold os.rmAllOutP os.rmPool os.rmSubOut
  iintro ⟨⟨%h', %hJ', Hb, HJ, %hsub, Ho⟩, %pool, Hpw, %hpool⟩
  obtain ⟨a1, a2, rfl, h1, h2⟩ := hpool.split
  have hcl : ClsSub (a1 ++ (J, NameSet.except [], hJ') :: a2) (l1 ++ (J, NameSet.except [], hJ0) :: l2) :=
    h1.append ⟨rfl, hsub, h2⟩
  iexists h', a1 ++ (J, NameSet.except [], hJ') :: a2
  iframe Hb
  isplitl [Hpw HJ]
  · iapply os.osClaimsW_put a1 a2 (J, NameSet.except [], hJ'); iframe
  icases Ho with (%he | ⟨%x, %s, -, %he⟩)
  · obtain ⟨rfl, hP⟩ := he
    ipureintro; exact ⟨EntsSub.refl _, hcl, fun hg => absurd hP (hG hg)⟩
  · ipureintro
    refine ⟨?_, hcl, fun _ => ?_⟩
    · rw [he.1]; simp only [NamesH.log]; exact EntsSub.restrictN_delete (EntsSub.refl _)
    · rw [he.1]
      simp [NamesH.log, restrictN_lookup _ _ _ (show (NameSet.only [b]).Mem b by simp [NameSet.Mem])]

/-- `rmAllOutP` of any `P` is one of `True`. -/
theorem os.rmAllOutP_true (j : Ino) (b : GoString) (J : Ino) (h hJ0 : NamesH) (P : Prop) :
    os.rmAllOutP (GF := GF) j b J h hJ0 P ⊢ os.rmAllOutP j b J h hJ0 True := by
  iintro H
  ihave H := os.rmAllOutP_out _ _ _ _ _ _ $$ H
  iapply os.rmAllOutP_of _ _ _ _ _ _ trivial $$ H

/-- `os.entsSub_merge1` from the name's claim holding some of what it held. -/
theorem os.entsSub_merge1' {J : Ino} {c : GoString} {hJ hc' h'' : NamesH} {e0 : Ents}
    (hsub : EntsSub hJ.cur e0) (hlo : EntsSub hc'.cur (hJ.restrict J (.only [c])).cur)
    (hm : h''.cur !! c = hc'.cur !! c ∧
      ∀ x, x ≠ c → h''.cur !! x = (hJ.restrict J (.except [c])).cur !! x) :
    EntsSub h''.cur e0 := by
  intro x n hx
  by_cases hxc : x = c
  · subst hxc
    rw [hm.1] at hx
    have := hlo x n hx
    simp only [NamesH.restrict] at this
    exact hsub x n (EntsSub.restrictN _ _ x n this)
  · rw [hm.2 x hxc] at hx
    simp only [NamesH.restrict] at hx
    exact hsub x n (EntsSub.restrictN _ _ x n hx)

/-- **`removeAllFrom(d, b)` of an entry holding anything**, with the claims `cl` of the directories
under it, at most `n` of them, under a guard of `d`'s root. -/
abbrev os.rmSubSpec (n : Nat) : Prop :=
  ∀ (d b : GoString) (j : Ino) (R : Roots) (qd : Qp) (h : NamesH) (cl : List Claim) (q g : Qp)
    (t sg : Nat) (pg : GoString),
  cl.length ≤ n → NameOk b → SubCover cl (h.cur !! b) → ClRanked cl → q + g = 1 →
  callKey R pg = callKey R d →
  {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗
      osNames j (.only [b]) (DFrac.own 1) h ∗ osClaimsW cl ∗ osCallPerm (callKey R d) q ∗
      osGuardS t sg pg g ∗ osLogLb sg }}
    (App (App (Val os.model.removeAllFrom) (Val #d)) (Val #b))
  {{ (pe : Loc), RET #pe; osPathS R d (DFrac.own qd) j ∗ osCallPerm (callKey R d) q ∗
      osGuardS t sg pg g ∗ os.peOk pe ∗ os.rmSubOut j b h cl (pe = null ∧ FsNoErrAt (child d b)) }}

/-- `removeAllFrom` of a name holding a file or nothing. -/
theorem os.model.wp_removeAllFrom_subLeaf (d b : GoString) (j : Ino) (R : Roots) (qd : Qp)
    (h : NamesH) (cl : List Claim) (q g : Qp) (t sg : Nat) (pg : GoString) (hb : NameOk b)
    (hnd : ∀ J, h.cur !! b ≠ some (.dir J)) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗
        osNames j (.only [b]) (DFrac.own 1) h ∗ osClaimsW cl ∗ osCallPerm (callKey R d) q ∗
        osGuardS t sg pg g ∗ osLogLb sg }}
      (App (App (Val os.model.removeAllFrom) (Val #d)) (Val #b))
    {{ (pe : Loc), RET #pe; osPathS R d (DFrac.own qd) j ∗ osCallPerm (callKey R d) q ∗
        osGuardS t sg pg g ∗ os.peOk pe ∗ os.rmSubOut j b h cl (pe = null ∧ FsNoErrAt (child d b)) }} := by
  iintro %Φ ⟨#Hos, #Hsi, Hp, Hn, Hcl, Hperm, Hg, #Hlsg⟩ HΦ
  wp_apply os.model.wp_removeAllFrom_leaf d b R j (DFrac.own qd) (DFrac.own 1) h q hb hnd (.inl rfl)
    $$ [Hp Hn Hperm] as %pe ⟨Hp, Hperm, Hpe, %h', Hn, %hlo⟩
  · iframe; iframe #
  iapply HΦ
  iframe
  unfold os.rmSubOut
  iexists h', cl
  iframe
  ipureintro; exact ⟨hlo.1.1, ClsSub.refl cl, fun hg => hlo.2 hg.2⟩

set_option hygiene false in
/-- `removeAllFrom`'s end after its passes: the `rmdir` loop, then the error (`pe`, the passes'). -/
local macro "rm_tailS" pe:term:max : tactic => `(tactic| (
  wp_apply os.model.wp_rmdirLoop_dirStW d b j J R qd h hJ0 q g t sg pg (hkg.trans (hkd b).symm) hb hJ hqg
    $$ [Hp Hst Hperm Hg] as %e4 ⟨Hp, Hst, Hperm, Hg⟩
  · iframe; iframe #
  by_cases he40 : e4 = W64 0
  · rw [decide_eq_true he40]
    try wp_auto
    iapply HΦ' $$ %null %(FsNoErrAt (child d b) → e4 = ENOTEMPTY)
      %(fun _ hne hP => by
        have := hP hne; rw [he40] at this; unfold ENOTEMPTY at this; exact absurd this (by decide))
    iframe
    iapply os.peOk_null
  rw [decide_eq_false he40]
  try wp_auto
  by_cases he42 : e4 = W64 2
  · rw [decide_eq_true he42]
    try wp_auto
    iapply HΦ' $$ %null %(FsNoErrAt (child d b) → e4 = ENOTEMPTY)
      %(fun _ hne hP => by
        have := hP hne; rw [he42] at this; unfold ENOTEMPTY at this; exact absurd this (by decide))
    iframe
    iapply os.peOk_null
  rw [decide_eq_false he42]
  try wp_auto
  ihave Hst := os.rmAllOutP_true _ _ _ _ _ _ $$ Hst
  by_cases hpn : $pe = null
  · simp only [decide_eq_true hpn, Bool.not_true]
    try wp_auto
    wp_apply os.model.wp_pathErrorPtr_errnoN _ _ e4 he40 as %pe' %hpn' Hpe'
    iapply HΦ' $$ %pe' %True %(fun h0 => absurd h0 hpn')
    iframe
  · simp only [decide_eq_false hpn, Bool.not_false]
    try wp_auto
    iapply HΦ' $$ %($pe) %True %(fun h0 => absurd h0 hpn)
    iframe))

set_option hygiene false in
/-- The spine to `d/b` given back, and the state rebuilt from `b`'s claim and `J`'s (`HJ`). -/
local macro "rm_restoreS" hs:term : tactic => `(tactic| (
  icases Hback $$ Hpc with ⟨Hp1, Hb⟩
  ihave Hp := (os.osPathS_halves R d qd j).1 $$ [Hp1 Hp2]
  · iframe
  ihave Hst : rmAllOut j b J h hJ0 $$ [Hb HJ]
  · iapply os.rmPresent_out; unfold os.rmPresent; iexists _; iframe; ipureintro; exact $hs))

theorem os.model.wp_removeAllFrom_subDir (n : Nat) (ih : os.rmSubSpec (GF := GF) n)
    (d b : GoString) (j J : Ino) (R : Roots) (qd : Qp) (h hJ0 : NamesH) (l1 l2 : List Claim)
    (q g : Qp) (t sg : Nat) (pg : GoString)
    (hlen : (l1 ++ (J, NameSet.except [], hJ0) :: l2).length ≤ n + 1) (hb : NameOk b)
    (hJ : h.cur !! b = some (.dir J))
    (hcov : SubCover (l1 ++ (J, NameSet.except [], hJ0) :: l2) (some (.dir J)))
    (hrk : ClRanked (l1 ++ (J, NameSet.except [], hJ0) :: l2)) (hqg : q + g = 1)
    (hkg : callKey R pg = callKey R d) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗ rmAllOut j b J h hJ0 ∗
        os.rmPool l1 l2 ∗ osCallPerm (callKey R d) q ∗ osGuardS t sg pg g ∗ osLogLb sg }}
      (App (App (Val os.model.removeAllFrom) (Val #d)) (Val #b))
    {{ (pe : Loc), RET #pe; osPathS R d (DFrac.own qd) j ∗ osCallPerm (callKey R d) q ∗
        osGuardS t sg pg g ∗ os.peOk pe ∗
        os.rmSubOut j b h (l1 ++ (J, NameSet.except [], hJ0) :: l2) (pe = null ∧ FsNoErrAt (child d b)) }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hst, Hpool, Hperm, Hg, #Hlsg⟩
  ihave HΦ' : (∀ (pe : Loc) (P : Prop), ⌜pe = null → FsNoErrAt (child d b) → ¬ P⌝ -∗
      osPathS R d (DFrac.own qd) j ∗ os.rmAllOutP j b J h hJ0 P ∗ os.rmPool l1 l2 ∗
      osCallPerm (callKey R d) q ∗ osGuardS t sg pg g ∗ os.peOk pe -∗ Φ #pe) $$ [HΦ]
  · iintro %pe %P %hP ⟨Hp, Hst, Hpool, Hperm, Hg, Hpe⟩
    iapply HΦ
    iframe
    iapply os.rmSubOut_ofP j b J h hJ0 l1 l2 P _ (fun hg => hP hg.1 hg.2) $$ [Hst Hpool]
    iframe
  icases osPathS_callKey R d _ j $$ Hp with ⟨Hp, %hkd⟩
  rw [show d ++ [47#8] ++ b = child d b by simp [child, slashB]]
  wp_apply os.model.wp_unlinkLoop_dirStW d b j J R (DFrac.own qd) h hJ0 q hb hJ $$ [Hp Hst Hperm]
    as %e ⟨%he0, Hp, Hst, Hperm⟩
  · iframe; iframe #
  rw [decide_eq_false (show e ≠ W64 0 from he0)]
  wp_auto
  by_cases he2 : e = W64 2
  · rw [decide_eq_true he2]
    wp_auto
    iapply HΦ' $$ %null %(FsNoErrAt (child d b) → e = EISDIR)
      %(fun _ hne hP => by have := hP hne; rw [he2] at this; unfold EISDIR at this; exact absurd this (by decide))
    iframe
    iapply os.peOk_null
  rw [decide_eq_false he2]
  wp_auto
  by_cases hcls : ¬ (e = W64 21 ∨ e = W64 1 ∨ e = W64 13)
  · simp only [not_or] at hcls
    obtain ⟨h21, h1, h13⟩ := hcls
    simp only [decide_eq_false h21, Bool.not_false]
    wp_auto
    simp only [decide_eq_false h1, Bool.not_false]
    wp_auto
    simp only [decide_eq_false h13, Bool.not_false]
    wp_auto
    wp_apply os.model.wp_pathErrorPtr_errnoN _ _ e he0 as %pe %hpn Hpe
    ihave Hst := os.rmAllOutP_true _ _ _ _ _ _ $$ Hst
    iapply HΦ' $$ %pe %True %(fun h0 => absurd h0 hpn)
    iframe
  rw [Classical.not_not] at hcls
  ihave Hst := os.rmAllOutP_out _ _ _ _ _ _ $$ Hst
  clear he2
  rcases hcls with rfl | rfl | rfl <;> wp_auto
  all_goals
    obtain ⟨r0, hr0⟩ : ∃ r : Loc, null = r := ⟨_, rfl⟩
    rw (occs := .pos [10]) [hr0]
    ihave Hrr : os.peOk r0 $$ []
    · rw [← hr0]; iapply os.peOk_null
    clear hr0
    iloeb as IH generalizing %r0 Hp Hst Hpool Hperm Hg Hrr HΦ'
    wp_apply os.model.wp_openLoop_dirStW d b j J R qd h hJ0 q hb hJ $$ [Hp Hst Hperm]
      as %fd %eo ⟨Hp, Hperm, Ho⟩
    · iframe; iframe #
    icases Ho with (⟨%heo, Hst⟩ | ⟨%heo, Hfd, Hpr⟩)
    · simp only [decide_eq_false (show eo ≠ W64 0 from heo), Bool.not_false]
      wp_auto
      by_cases heo2 : eo = W64 2
      · rw [decide_eq_true heo2]
        wp_auto
        iapply HΦ' $$ %null %(eo ≠ W64 2) %(fun _ _ hP => hP heo2)
        iframe
        iapply os.peOk_null
      rw [decide_eq_false heo2]
      wp_auto
      ihave Hst := os.rmAllOutP_out _ _ _ _ _ _ $$ Hst
      by_cases heo20 : eo = W64 20
      · rw [decide_eq_true heo20]
        wp_auto
        wp_apply os.model.wp_pathErrorPtr_errnoN _ _ _ (by decide) as %pe %hpn Hpe
        try wp_auto
        ihave Hst := os.rmAllOutP_of _ _ _ _ _ True trivial $$ Hst
        iapply HΦ' $$ %pe %True %(fun h0 => absurd h0 hpn)
        iframe
      rw [decide_eq_false heo20]
      wp_auto
      wp_apply os.model.wp_pathErrorPtr_errno _ _ _ heo as %pe Hpe
      try wp_auto
      rm_tailS pe
    · simp only [decide_eq_true (show eo = W64 0 from heo), Bool.not_true]
      wp_auto
      wp_apply wp_osFdKindDirS fd J .idle CoPset.subseteq_top $$ Hos Hfd as Hfd
      unfold os.rmPresent
      icases Hpr with ⟨%hJ', Hb, HJ, %hsub⟩
      icases (os.osPathS_halves R d qd j).2 $$ Hp with ⟨Hp1, Hp2⟩
      icases os.osPathS_borrow R d b j J qd.half h hb hJ $$ [Hp1 Hb] with ⟨%ε, Hpc, Hback⟩
      · iframe
      -- the read of all names
      wp_apply wp_slice_literal (V := GoString) []
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, Hcap⟩
      simp only [go.arrayLiteralSize, List.foldl]
      obtain ⟨fresh, hfresh⟩ : ∃ b : Bool, b = true := ⟨_, rfl⟩
      obtain ⟨rs, hrs⟩ : ∃ rs : List GoString, rs = [] := ⟨_, rfl⟩
      obtain ⟨rr0, -⟩ : ∃ r0 : Nat, r0 = 0 := ⟨_, rfl⟩
      ihave Hfd : osDirFdS fd J (if fresh then .idle else .reading (.except []) rr0 rs) $$ [Hfd]
      · subst hfresh; simp only [↓reduceIte]; iexact Hfd
      generalize hsl0 : slice.mk _ _ _ = sl0
      ihave Hsl : sl0 ↦* rs.reverse $$ [Hsl]
      · subst hrs; rw [List.reverse_nil]; iexact Hsl
      ihave Hpu : ⌜(fresh = true → rs = []) ∧ (fresh = false → hJ'.next ≤ rr0) ∧
          (∀ x ∈ rs, NameOk x)⌝ $$ []
      · ipureintro; subst hrs hfresh; simp
      clear hfresh hrs hsl0
      wp_auto
      iloeb as IHr generalizing %fresh %rs %rr0 %sl0 Hpu Hfd Hsl Hcap HJ Hpool
      icases Hpu with %Hpu
      obtain ⟨hfr, hr0, hin⟩ := Hpu
      wp_apply wp_osDirReadNextGenS' R fd J (.except []) rr0 rs fresh (DFrac.own 1) hJ'
        (osPathS R (child d b) (DFrac.own ε) J) (fun st => st.lookup (child d b) = some (.dir J)) False
        (fun st Γn hR hcoh => by
          iintro HA Hpc
          icases osPathS_lookup hR hcoh (child d b) _ J $$ HA Hpc with %h1
          ipureintro; exact h1)
        (fun st _ hl hn => hn (reach_of_lookup hl)) hfr hr0
        CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hfd HJ Hpc
        as %v HJ Hpc ⟨%rr0', %hr1, %hr2, Hv⟩
      icases Hv with (⟨%c, %hv, Hfd⟩ | ⟨%hv, Hfd⟩ | ⟨%e, %hv, Hfd⟩)
      · obtain ⟨rfl, hc, hcr⟩ := hv
        wp_auto
        wp_apply wp_slice_literal (V := GoString) [c]
        isplitr
        · ipureintro; rfl
        iintro %sl1 ⟨Hsl1, -⟩
        wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl1] as %sl' ⟨Hsl, Hcap, -⟩
        iapply IHr $$ %false %(c :: rs) %rr0' %sl' [] [Hfd] [Hsl] Hcap HJ Hpool Hg Hrr HΦ' Hperm Hp2 Hpc Hback
        · ipureintro
          refine ⟨fun h => absurd h Bool.false_ne_true, fun _ => ?_, ?_⟩
          · cases fresh
            · rw [hr1 rfl]; exact hr0 rfl
            · exact hr2 rfl
          · intro x hx
            rcases List.mem_cons.1 hx with rfl | hx
            · exact hc
            · exact hin x hx
        · simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hfd
        · rw [List.reverse_cons]; iexact Hsl
      · obtain ⟨rfl, hall⟩ := hv
        wp_auto
        obtain ⟨k0, hk0, hk0'⟩ : ∃ k : Nat, (W64 0 : w64) = W64 (k : Int) ∧ k = 0 := ⟨0, rfl, rfl⟩
        rw (occs := .pos [69, 70]) [hk0]
        rw [show decide (W64 0 = sl0.len) = decide (W64 ((k0 : Nat) : Int) = sl0.len) by rw [← hk0]]
        icases ownSlice_len sl0 _ _ $$ Hsl with %Hlen
        ihave Hpe : ⌜k0 ≤ rs.reverse.length ∧ EntsSub hJ'.cur hJ0.cur⌝ $$ []
        · ipureintro; exact ⟨by omega, hsub⟩
        iclear IHr
        clear hk0 hk0' hr0 hr1 hr2 hall hsub hfr
        iloeb as IHe generalizing %k0 %r0 %hJ' Hpe Hrr HJ Hpool
        icases Hpe with %hpe
        obtain ⟨hk, hsubk⟩ := hpe
        by_cases hkn : k0 = rs.reverse.length
        · rw [decide_eq_true (show W64 ((k0 : Nat) : Int) = sl0.len by
            have h1 := Hlen.1; have h2 := Hlen.2; rw [hkn, h1]; word)]
          wp_auto
          wp_apply wp_osDirCloseS fd J _ CoPset.subseteq_top $$ Hos Hfd as %ec
          rm_restoreS hsubk
          wp_apply wp_ArbitraryInt as %y _
          by_cases hy : y = W64 0
          · subst hy
            wp_auto
            rm_tailS r0
          · rw [decide_eq_false hy]
            wp_auto
            iapply IH $$ %r0 Hp Hst Hpool Hperm Hg Hrr HΦ'
        · rw [decide_eq_false (show W64 ((k0 : Nat) : Int) ≠ sl0.len by
            have h1 := Hlen.1; have h2 := Hlen.2; intro h; apply hkn; rw [h1, ← h]; word)]
          wp_auto
          have hkl : k0 < rs.reverse.length := by omega
          have h1 := Hlen.1
          have h2 := Hlen.2
          rw [if_pos (show 0 ≤ sint.Z (W64 ((k0 : Nat) : Int)) ∧
              sint.Z (W64 ((k0 : Nat) : Int)) < sint.Z sl0.len by
            constructor <;> word)]
          obtain ⟨c, hcget⟩ : ∃ c, rs.reverse[k0]? = some c := ⟨_, List.getElem?_eq_getElem hkl⟩
          wp_apply wp_load_slice_index sl0 (sint.Z (W64 ((k0 : Nat) : Int))) rs.reverse (DFrac.own 1) c
            (by word) $$ [Hsl] as Hsl
          · iframe; ipureintro
            rw [show (sint.Z (W64 ((k0 : Nat) : Int))).toNat = k0 by word]; exact hcget
          have hcN : NameOk c := hin c (List.mem_reverse.1 (List.mem_of_getElem? hcget))
          imod os.osNames_split1 R J c hJ' $$ Hsi HJ with ⟨Hc, Hr⟩
          iunfold os.rmPool at Hpool
          icases Hpool with ⟨%pool, Hpw, %hpool⟩
          have hlp : pool.length ≤ n := by
            rw [hpool.length]; simp only [List.length_append, List.length_cons] at hlen ⊢; omega
          have hcovc : SubCover pool ((hJ'.restrict J (.only [c])).cur !! c) := by
            rw [os.restrict_only_cur]
            rcases hcc : hJ'.cur !! c with _ | ⟨i | K⟩
            · exact SubCover.not_dir (fun _ h => by cases h)
            · exact SubCover.not_dir (fun _ h => by cases h)
            · exact subCover_pool hcov hrk hpool (hsubk c _ hcc)
          wp_apply ih (child d b) c J R ε (hJ'.restrict J (.only [c])) pool q g t sg pg hlp hcN hcovc
            (ClRanked.pool hrk hpool) hqg (hkg.trans (hkd b).symm) $$ [Hpc Hc Hpw Hperm Hg]
            as %pe ⟨Hpc, Hperm, Hg, Hpe, Hout⟩
          · rw [hkd b]; iframe; iframe #
          rw [hkd b]
          iunfold os.rmSubOut at Hout
          icases Hout with ⟨%hc', %pool', Hc, Hpw, %hout⟩
          ihave Hpool : os.rmPool l1 l2 $$ [Hpw]
          · unfold os.rmPool; iexists pool'; iframe; ipureintro; exact hout.2.1.trans hpool
          imod os.osNames_merge1 R J c hc' (hJ'.restrict J (.except [c])) $$ Hsi Hc Hr
            with ⟨%h'', HJ, %hm⟩
          have hsub'' : EntsSub h''.cur hJ0.cur := os.entsSub_merge1' hsubk hout.1 hm
          wp_apply os.model.wp_prefixPath pe b $$ Hpe as Hpe
          by_cases hrn : r0 = null
          · rw [decide_eq_true hrn]
            wp_auto
            rw [show W64 ((k0 : Nat) : Int) + W64 1 = W64 ((k0 + 1 : Nat) : Int) by word]
            iapply IHe $$ %(k0 + 1) %pe %h'' [] Hpe HJ Hpool Hsl Hcap Hg HΦ' Hperm Hp2 Hback Hpc Hfd
            · ipureintro; exact ⟨by omega, hsub''⟩
          · rw [decide_eq_false hrn]
            wp_auto
            rw [show W64 ((k0 : Nat) : Int) + W64 1 = W64 ((k0 + 1 : Nat) : Int) by word]
            iapply IHe $$ %(k0 + 1) %r0 %h'' [] Hrr HJ Hpool Hsl Hcap Hg HΦ' Hperm Hp2 Hback Hpc Hfd
            · ipureintro; exact ⟨by omega, hsub''⟩
      · obtain ⟨he, rfl, hgo⟩ := hv
        wp_auto
        by_cases he4 : e = W64 4
        · rw [decide_eq_true he4]
          wp_auto
          iapply IHr $$ %false %rs %rr0' %sl0 [] [Hfd] Hsl Hcap HJ Hpool Hg Hrr HΦ' Hperm Hp2 Hpc Hback
          · ipureintro
            refine ⟨fun h => absurd h Bool.false_ne_true, fun _ => ?_, hin⟩
            cases fresh
            · rw [hr1 rfl]; exact hr0 rfl
            · exact hr2 rfl
          · simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hfd
        · rw [decide_eq_false he4]
          wp_auto
          simp only [decide_eq_false (show e ≠ W64 0 from he), Bool.not_false]
          wp_auto
          simp only [decide_eq_false (show e ≠ W64 0 from he), Bool.not_false]
          wp_auto
          wp_apply wp_osDirCloseS fd J _ CoPset.subseteq_top $$ Hos Hfd as %ec
          rm_restoreS hsub
          by_cases he2 : e = W64 2
          · exact (hgo (by rw [he2]; rfl)).elim
          rw [decide_eq_false he2]
          wp_auto
          wp_apply os.model.wp_pathErrorPtr_rdN _ e he as %pe %hpn Hpe
          try wp_auto
          ihave Hst := os.rmAllOutP_of _ _ _ _ _ True trivial $$ Hst
          iapply HΦ' $$ %pe %True %(fun h0 => absurd h0 hpn)
          iframe


theorem os.model.wp_removeAllFrom_sub (n : Nat) : os.rmSubSpec (GF := GF) n := by
  induction n with
  | zero =>
    intro d b j R qd h cl q g t sg pg hlen hb hcov hrk hqg hkg
    refine os.model.wp_removeAllFrom_subLeaf d b j R qd h cl q g t sg pg hb (fun J hJ => ?_)
    obtain ⟨hJ0, hm⟩ := hcov J hJ J (.refl J)
    have := List.length_pos_of_mem hm
    omega
  | succ n ih =>
    intro d b j R qd h cl q g t sg pg hlen hb hcov hrk hqg hkg
    rcases hJ : h.cur !! b with _ | ⟨i | J⟩
    · exact os.model.wp_removeAllFrom_subLeaf d b j R qd h cl q g t sg pg hb
        (fun J h' => by rw [hJ] at h'; cases h')
    · exact os.model.wp_removeAllFrom_subLeaf d b j R qd h cl q g t sg pg hb
        (fun J h' => by rw [hJ] at h'; cases h')
    · rw [hJ] at hcov
      obtain ⟨hJ0, hm⟩ := hcov J rfl J (.refl J)
      obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hm
      iintro %Φ ⟨#Hos, #Hsi, Hp, Hn, Hcl, Hperm, Hg, #Hlsg⟩ HΦ
      icases os.osClaimsW_take l1 l2 _ $$ Hcl with ⟨Hpw, HJ⟩
      ihave Hst : rmAllOut j b J h hJ0 $$ [Hn HJ]
      · iapply os.rmPresent_out; unfold os.rmPresent; iexists hJ0; iframe; ipureintro
        exact EntsSub.refl _
      ihave Hpool : os.rmPool l1 l2 $$ [Hpw]
      · unfold os.rmPool; iexists l1 ++ l2; iframe; ipureintro; exact ClsSub.refl _
      wp_apply os.model.wp_removeAllFrom_subDir n ih d b j J R qd h hJ0 l1 l2 q g t sg pg hlen hb hJ
        hcov hrk hqg hkg $$ [Hp Hst Hpool Hperm Hg] as %pe Hres
      · iframe; iframe #
      iapply HΦ $$ Hres

/-- `EntsSub` keeps an absent name absent. -/
theorem os.entsSub_none {a b : Ents} {x : GoString} (h : EntsSub a b) (hb : b !! x = none) :
    a !! x = none := by
  rcases ha : a !! x with _ | n
  · rfl
  · rw [h x n ha] at hb; cases hb

set_option hygiene false in
/-- The end of `RemoveAll` (`RemoveAll.lean`'s `rm_fin`, the whole call permission, the claims' state
`Hout`, a `rmSubOut … G`, built; `w` turns its `G → b gone` into the post's witness). -/
local macro "rm_finS" w:term:max fin:tacticSeq : tactic => `(tactic| (
  try wp_auto
  wp_apply wp_osLstatDirGuardS R (child d b) t sg (1 : Qp).half hp CoPset.subseteq_top
    CoPset.subseteq_top $$ Hos Hsi Hg as %isDir %e5 %- Hg
  icases osCallPerm_unchild R d b _ _ _ $$ Hp Hg with ⟨Hp, Hg⟩
  iunfold os.rmSubOut at Hout
  icases Hout with ⟨%hh', %cl'', Hn', Hcl', %hpo⟩
  iapply HΦ
  iframe Hp
  isplitl [Hperm Hg]
  · iapply (os.osCallPerm_halves _ (1 : Qp)).1; iframe
  isplitl [Hn' Hcl']
  · iexists hh', cl''; iframe; ipureintro; exact ⟨hpo.1, hpo.2.1, $w hpo.2.2⟩
  ($fin)))

set_option hygiene false in
/-- The claims' state of a name holding a file or nothing (`Hn`, its entries `hs` some of `h`'s; `hg`:
it holds nothing at `b` when the file system does not fail on `d/b`). -/
local macro "mk_outL" hs:term:max hg:term:max : tactic => `(tactic| (
  ihave Hout : os.rmSubOut j b h cl (FsNoErrAt (child d b)) $$ [Hn Hcl]
  · unfold os.rmSubOut; iexists _, cl; iframe; ipureintro; exact ⟨$hs, ClsSub.refl cl, $hg⟩))

set_option hygiene false in
/-- The claims' state of a directory's removal (`Hst`, a `rmAllOutP … P`, `Hpool`), `b` gone when `G`
(`hG : G → ¬ P`). -/
local macro "mk_outD" P:term:max G:term:max hG:term:max : tactic => `(tactic| (
  ihave Hout : os.rmSubOut j b h (l1 ++ (J, NameSet.except [], hJ0) :: l2) $G $$ [Hst Hpool]
  · iapply os.rmSubOut_ofP j b J h hJ0 l1 l2 $P $G $hG; iframe))

/-- `fmtErrorOk` is not `nil`. -/
theorem os.fmtErrorOk_ne_nil (err : GoInterface) :
    fmtErrorOk (GF := GF) err ⊢ ⌜err ≠ interface.nil⌝ := by
  cases err with
  | nil => unfold fmtErrorOk; iintro H; iexfalso; iexact H
  | ok ii => iintro -; ipureintro; intro h; cases h

theorem os.RemoveAll.wp_proofSubS : os.RemoveAll.specSubS (GF := GF) (hG := hG) := by
  intro d b j R qd h cl hb hcov hrk
  wp_start as ⟨#Hos, #Hsi, Hp, Hn, Hcl, Hperm⟩
  icases os.osPathS_facts R d _ j b hb $$ Hp with %hpf
  obtain ⟨hd, hp⟩ := hpf
  icases osPathS_callKey R d _ j $$ Hp with ⟨Hp, %hkd⟩
  rw [decide_eq_false (show child d b ≠ [] by simp [child])]
  wp_auto
  wp_apply os.wp_endsWithDot_child d b hb
  imod osLogLb_0 with #Hlb
  icases (os.osCallPerm_halves _ 1).2 $$ Hperm with ⟨Hg, Hperm⟩
  icases osCallPerm_child R d b _ _ _ $$ Hp Hg with ⟨Hp, Hg⟩
  wp_apply +noauto wp_osCallBeginGuardS R _ (1 : Qp).half 0 CoPset.subseteq_top
    CoPset.subseteq_top $$ Hos Hsi Hg Hlb as %t %sg %- Hg #Hlsg
  wp_auto
  have hqg : (1 : Qp).half + (1 : Qp).half = 1 := Qp.half_add_half 1
  by_cases hdir : ∃ J, h.cur !! b = some (.dir J)
  case neg =>
    have hnd : ∀ J, h.cur !! b ≠ some (.dir J) := fun J h' => hdir ⟨J, h'⟩
    wp_apply os.model.wp_unlinkLoop_leaf d b R j (DFrac.own qd) (DFrac.own 1) h (1 : Qp).half hb hnd
      (.inl rfl) $$ [Hp Hn Hperm] as %e ⟨Hp, Hperm, %h', Hn, %hlow⟩
    · iframe; iframe #
    obtain ⟨hlo, hlw⟩ := hlow
    have hnd' : ∀ J, h'.cur !! b ≠ some (.dir J) := fun J h2 => hnd J (hlo.1 b _ h2)
    by_cases he0 : e = W64 0
    · rw [decide_eq_true he0]
      mk_outL hlo.1 hlw
      rm_finS (fun hg _ hne _ => hg hne)
        simp only [fmtErrorOkOrNil]; itrivial
    rw [decide_eq_false he0]
    wp_auto
    wp_apply os.model.wp_rmdirLoop_none d b R j (DFrac.own qd) (DFrac.own 1) _ (1 : Qp).half hb hnd'
      $$ [Hp Hn Hperm] as %e1 ⟨%he1, Hp, Hn, Hperm⟩
    · iframe; iframe #
    rw [decide_eq_false (show e1 ≠ W64 0 from he1)]
    wp_auto
    by_cases he20 : e1 = W64 20
    all_goals first
      | (simp only [decide_eq_true he20, Bool.not_true]; wp_auto; generalize e = e2)
      | (simp only [decide_eq_false he20, Bool.not_false]; wp_auto; generalize e1 = e2)
    all_goals
      by_cases he22 : e2 = W64 2
      · rw [decide_eq_true he22]
        mk_outL hlo.1 hlw
        rm_finS (fun hg _ hne _ => hg hne)
          simp only [fmtErrorOkOrNil]; itrivial
      rw [decide_eq_false he22]
      wp_auto
      wp_apply os.wp_splitPath_child d b hb hd
      wp_apply os.model.wp_openLoop_spine d R j (DFrac.own qd) (1 : Qp).half $$ [Hp Hperm]
        as %fd %eo ⟨Hp, Hperm, Ho⟩
      · iframe; iframe #
      icases Ho with (%heo | ⟨%heo, Hfd⟩)
      · by_cases heo2 : eo = W64 2
        · rw [decide_eq_true heo2]
          mk_outL hlo.1 hlw
          rm_finS (fun hg _ hne _ => hg hne)
            simp only [fmtErrorOkOrNil]; itrivial
        rw [decide_eq_false heo2]
        wp_auto
        simp only [decide_eq_false (show eo ≠ W64 0 from heo), Bool.not_false]
        wp_auto
        wp_apply os.wp_pathError_ok _ _ eo heo as %pe #Hok
        mk_outL hlo.1 hlw
        rm_finS (fun hg _ hne _ => hg hne)
          iapply (EtcdGrove.fmtErrorOkOrNil_of _) $$ Hok
      · rw [decide_eq_false (show eo ≠ W64 2 by rw [heo]; decide)]
        wp_auto
        simp only [decide_eq_true (show eo = W64 0 from heo), Bool.not_true]
        wp_auto
        wp_apply os.model.wp_removeAllFrom_leaf d b R j (DFrac.own qd) (DFrac.own 1) h' (1 : Qp).half
          hb hnd' (.inl rfl) $$ [Hp Hn Hperm] as %pe ⟨Hp, Hperm, Hpe, %h'', Hn, %hlow'⟩
        · iframe; iframe #
        obtain ⟨hlo', -⟩ := hlow'
        wp_apply os.model.wp_closeFd_dir fd j _ $$ [Hfd]
        · iframe; iframe #
        by_cases hpn : pe = null
        · rw [decide_eq_true hpn]
          mk_outL (hlo'.1.trans hlo.1) (fun hne => os.entsSub_none hlo'.1 (hlw hne))
          rm_finS (fun hg _ hne _ => hg hne)
            simp only [fmtErrorOkOrNil]; itrivial
        rw [decide_eq_false hpn]
        wp_auto
        wp_apply os.model.wp_prefixPath pe d $$ Hpe as Hpe
        imod os.peOk_fmt pe hpn $$ Hpe with #Hok
        mk_outL (hlo'.1.trans hlo.1) (fun hne => os.entsSub_none hlo'.1 (hlw hne))
        rm_finS (fun hg _ hne _ => hg hne)
          iexact Hok
  case pos =>
    obtain ⟨J, hbJ⟩ := hdir
    rw [hbJ] at hcov
    obtain ⟨hJ0, hm⟩ := hcov J rfl J (.refl J)
    obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hm
    icases os.osClaimsW_take l1 l2 _ $$ Hcl with ⟨Hpw, HJ⟩
    ihave Hst : rmAllOut j b J h hJ0 $$ [Hn HJ]
    · iapply os.rmPresent_out; unfold os.rmPresent; iexists hJ0; iframe; ipureintro
      exact EntsSub.refl _
    ihave Hpool : os.rmPool l1 l2 $$ [Hpw]
    · unfold os.rmPool; iexists l1 ++ l2; iframe; ipureintro; exact ClsSub.refl _
    wp_apply os.model.wp_unlinkLoop_dirSt d b j J R (DFrac.own qd) h hJ0 (1 : Qp).half hb hbJ
      $$ [Hp Hst Hperm] as %e ⟨%he0, Hp, Hst, Hperm⟩
    · iframe; iframe #
    rw [decide_eq_false (show e ≠ W64 0 from he0)]
    wp_auto
    wp_apply os.model.wp_rmdirLoop_dirStW d b j J R qd h hJ0 (1 : Qp).half (1 : Qp).half t sg (child d b)
      rfl hb hbJ hqg $$ [Hp Hst Hperm Hg] as %e1 ⟨Hp, Hst, Hperm, Hg⟩
    · iframe; iframe #
    by_cases he10 : e1 = W64 0
    · rw [decide_eq_true he10]
      mk_outD (FsNoErrAt (child d b) → e1 = ENOTEMPTY) (FsNoErrAt (child d b))
        (fun hne hP => by have := hP hne; rw [he10] at this; unfold ENOTEMPTY at this; exact absurd this (by decide))
      rm_finS (fun hg _ hne _ => hg hne)
        simp only [fmtErrorOkOrNil]; itrivial
    rw [decide_eq_false he10]
    wp_auto
    by_cases he20 : e1 = W64 20
    all_goals first
      | (simp only [decide_eq_true he20, Bool.not_true]; wp_auto; generalize e = e2)
      | (simp only [decide_eq_false he20, Bool.not_false]; wp_auto; generalize e1 = e2)
    all_goals
      by_cases he22 : e2 = W64 2
      · rw [decide_eq_true he22]
        first
          | mk_outD (FsNoErrAt (child d b) → e1 = ENOTEMPTY) (FsNoErrAt (child d b))
              (fun hne hP => by
                have := hP hne; rw [he20] at this; unfold ENOTEMPTY at this; exact absurd this (by decide))
          | mk_outD (FsNoErrAt (child d b) → e2 = ENOTEMPTY) (FsNoErrAt (child d b))
              (fun hne hP => by
                have := hP hne; rw [he22] at this; unfold ENOTEMPTY at this; exact absurd this (by decide))
        rm_finS (fun hg _ hne _ => hg hne)
          simp only [fmtErrorOkOrNil]; itrivial
      rw [decide_eq_false he22]
      wp_auto
      wp_apply os.wp_splitPath_child d b hb hd
      wp_apply os.model.wp_openLoop_spineW d R j (DFrac.own qd) (1 : Qp).half $$ [Hp Hperm]
        as %fd %eo ⟨Hp, Hperm, Ho⟩
      · iframe; iframe #
      icases Ho with (%heo | ⟨%heo, Hfd⟩)
      · by_cases heo2 : eo = W64 2
        · exact absurd heo2 heo.2
        rw [decide_eq_false heo2]
        wp_auto
        simp only [decide_eq_false (show eo ≠ W64 0 from heo.1), Bool.not_false]
        wp_auto
        wp_apply os.wp_pathError_ok _ _ eo heo.1 as %pe #Hok
        icases os.fmtErrorOk_ne_nil _ $$ Hok with %hne0
        ihave Hst := os.rmAllOutP_true _ _ _ _ _ _ $$ Hst
        mk_outD True False (fun h0 => h0.elim)
        rm_finS (fun _ h0 => absurd h0 hne0)
          iapply (EtcdGrove.fmtErrorOkOrNil_of _) $$ Hok
      · rw [decide_eq_false (show eo ≠ W64 2 by rw [heo]; decide)]
        wp_auto
        simp only [decide_eq_true (show eo = W64 0 from heo), Bool.not_true]
        wp_auto
        ihave Hst := os.rmAllOutP_out _ _ _ _ _ _ $$ Hst
        wp_apply os.model.wp_removeAllFrom_subDir _ (os.model.wp_removeAllFrom_sub _) d b j J R qd h
          hJ0 l1 l2 (1 : Qp).half (1 : Qp).half t sg (child d b) (Nat.le_succ _) hb hbJ hcov hrk hqg
          (hkd b) $$ [Hp Hst Hpool Hperm Hg] as %pe ⟨Hp, Hperm, Hg, Hpe, Hout⟩
        · iframe; iframe #
        wp_apply os.model.wp_closeFd_dir fd j _ $$ [Hfd]
        · iframe; iframe #
        by_cases hpn : pe = null
        · rw [decide_eq_true hpn]
          rm_finS (fun hg _ hne _ => hg ⟨hpn, hne⟩)
            simp only [fmtErrorOkOrNil]; itrivial
        rw [decide_eq_false hpn]
        wp_auto
        wp_apply os.model.wp_prefixPath pe d $$ Hpe as Hpe
        imod os.peOk_fmt pe hpn $$ Hpe with #Hok
        rm_finS (fun _ h0 => by cases h0)
          iexact Hok

end proof

end EtcdGrove
end Perennial

end
