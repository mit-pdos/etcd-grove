/-
`os.RemoveAll`'s `model.removeAllFrom` on the directory it removes (`d/b`, the directory `J` whose
entries are files), in the tree's shared mode, under `RemoveAll`'s guard, for
`Proof/os/RemoveAll.lean`: its passes (each an open of `J`, a read of all its names with the whole
claim on them, the removal of each name, `Proof/os/RemoveAllLeaf.lean`), then its `rmdir`.
Lean-first; untrusted.
-/
module

public import LinuxFs.Proof.os.RemoveAllDir

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
variable [os.Assumptions] [os.fileStat.FieldAssumptions]

/-- A spine's two halves. -/
theorem os.osPathS_halves (R : Roots) (d : GoString) (qd : Qp) (j : Ino) :
    osPathS (GF := GF) R d (DFrac.own qd.half) j ∗ osPathS R d (DFrac.own qd.half) j ⊣⊢
      osPathS R d (DFrac.own qd) j := by
  have h := osPathS_frac (GF := GF) R d qd.half qd.half j
  rw [Qp.half_add_half] at h
  exact ⟨h.2, h.1⟩

set_option hygiene false in
/-- `removeAllFrom`'s end after its passes: the `rmdir` loop, then the error (`pe`, the passes'). -/
local macro "rm_tail" pe:term:max : tactic => `(tactic| (
  wp_apply os.model.wp_rmdirLoop_dirSt d b j J R qd h hJ0 q g t sg hb hJ hqg
    $$ [Hp Hst Hperm Hg] as %e4 ⟨Hp, Hst, Hperm, Hg⟩
  · iframe; iframe #
  by_cases he40 : e4 = W64 0
  · rw [decide_eq_true he40]
    try wp_auto
    iapply HΦ
    iframe
    iapply os.peOk_null
  rw [decide_eq_false he40]
  try wp_auto
  by_cases he42 : e4 = W64 2
  · rw [decide_eq_true he42]
    try wp_auto
    iapply HΦ
    iframe
    iapply os.peOk_null
  rw [decide_eq_false he42]
  try wp_auto
  by_cases hpn : $pe = null
  · simp only [decide_eq_true hpn, Bool.not_true]
    try wp_auto
    wp_apply os.model.wp_pathErrorPtr_errno _ _ e4 he40 as %pe' Hpe'
    iapply HΦ
    iframe
  · simp only [decide_eq_false hpn, Bool.not_false]
    try wp_auto
    iapply HΦ
    iframe))

set_option hygiene false in
/-- The spine to `d/b` given back, and the state rebuilt from `b`'s claim and `J`'s (`HJ`). -/
local macro "rm_restore" hs:term : tactic => `(tactic| (
  icases Hback $$ Hpc with ⟨Hp1, Hb⟩
  ihave Hp := (os.osPathS_halves R d qd j).1 $$ [Hp1 Hp2]
  · iframe
  ihave Hst : rmAllOut j b J h hJ0 $$ [Hb HJ]
  · iapply os.rmPresent_out; unfold os.rmPresent; iexists _; iframe; ipureintro; exact $hs))

theorem os.model.wp_removeAllFrom_dir (d b : GoString) (j J : Ino) (R : Roots) (qd : Qp)
    (h hJ0 : NamesH) (q g : Qp) (t sg : Nat) (hb : NameOk b) (hJ : h.cur !! b = some (.dir J))
    (hfo : FilesOnly hJ0.cur) (hqg : q + g = 1) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗ rmAllOut j b J h hJ0 ∗
        osCallPerm q ∗ osGuardS t sg g ∗ osLogLb sg }}
      (App (App (Val os.model.removeAllFrom) (Val #d)) (Val #b))
    {{ (pe : Loc), RET #pe; osPathS R d (DFrac.own qd) j ∗ rmAllOut j b J h hJ0 ∗ osCallPerm q ∗
        osGuardS t sg g ∗ os.peOk pe }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hst, Hperm, Hg, #Hlsg⟩
  rw [show d ++ [47#8] ++ b = child d b by simp [child, slashB]]
  wp_apply os.model.wp_unlinkLoop_dirSt d b j J R (DFrac.own qd) h hJ0 q hb hJ $$ [Hp Hst Hperm]
    as %e ⟨%he0, Hp, Hst, Hperm⟩
  · iframe; iframe #
  rw [decide_eq_false (show e ≠ W64 0 from he0)]
  wp_auto
  by_cases he2 : e = W64 2
  · rw [decide_eq_true he2]
    wp_auto
    iapply HΦ
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
    wp_apply os.model.wp_pathErrorPtr_errno _ _ e he0 as %pe Hpe
    iapply HΦ
    iframe
  rw [Classical.not_not] at hcls
  clear he2
  rcases hcls with rfl | rfl | rfl <;> wp_auto
  all_goals
    obtain ⟨r0, hr0⟩ : ∃ r : Loc, null = r := ⟨_, rfl⟩
    rw (occs := .pos [9]) [hr0]
    ihave Hrr : os.peOk r0 $$ []
    · rw [← hr0]; iapply os.peOk_null
    clear hr0
    iloeb as IH generalizing %r0 Hp Hst Hperm Hg Hrr HΦ
    wp_apply os.model.wp_openLoop_dirSt d b j J R qd h hJ0 q hb hJ $$ [Hp Hst Hperm]
      as %fd %eo ⟨Hp, Hperm, Ho⟩
    · iframe; iframe #
    icases Ho with (⟨%heo, Hst⟩ | ⟨%heo, Hfd, Hpr⟩)
    · simp only [decide_eq_false (show eo ≠ W64 0 from heo), Bool.not_false]
      wp_auto
      by_cases heo2 : eo = W64 2
      · rw [decide_eq_true heo2]
        wp_auto
        iapply HΦ
        iframe
        iapply os.peOk_null
      rw [decide_eq_false heo2]
      wp_auto
      by_cases heo20 : eo = W64 20
      · rw [decide_eq_true heo20]
        wp_auto
        wp_apply os.model.wp_pathErrorPtr_errno _ _ _ (by decide) as %pe Hpe
        try wp_auto
        iapply HΦ
        iframe
      rw [decide_eq_false heo20]
      wp_auto
      wp_apply os.model.wp_pathErrorPtr_errno _ _ _ heo as %pe Hpe
      try wp_auto
      rm_tail pe
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
      iloeb as IHr generalizing %fresh %rs %rr0 %sl0 Hpu Hfd Hsl Hcap HJ
      icases Hpu with %Hpu
      obtain ⟨hfr, hr0, hin⟩ := Hpu
      wp_apply wp_osDirReadNextS R fd J (.except []) rr0 rs fresh (DFrac.own 1) hJ' hfr hr0
        CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hfd HJ
        as %v HJ ⟨%rr0', %hr1, %hr2, Hv⟩
      icases Hv with (⟨%c, %hv, Hfd⟩ | ⟨%hv, Hfd⟩ | ⟨%e, %hv, Hfd⟩)
      · obtain ⟨rfl, hc, hcr⟩ := hv
        wp_auto
        wp_apply wp_slice_literal (V := GoString) [c]
        isplitr
        · ipureintro; rfl
        iintro %sl1 ⟨Hsl1, -⟩
        wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl1] as %sl' ⟨Hsl, Hcap, -⟩
        iapply IHr $$ %false %(c :: rs) %rr0' %sl' [] [Hfd] [Hsl] Hcap HJ Hg Hrr HΦ Hperm Hp2 Hpc Hback
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
        iloeb as IHe generalizing %k0 %r0 %hJ' Hpe Hrr HJ
        icases Hpe with %hpe
        obtain ⟨hk, hsubk⟩ := hpe
        by_cases hkn : k0 = rs.reverse.length
        · rw [decide_eq_true (show W64 ((k0 : Nat) : Int) = sl0.len by
            have h1 := Hlen.1; have h2 := Hlen.2; rw [hkn, h1]; word)]
          wp_auto
          wp_apply wp_osDirCloseS fd J _ CoPset.subseteq_top $$ Hos Hfd as %ec
          rm_restore hsubk
          wp_apply wp_ArbitraryInt as %y _
          by_cases hy : y = W64 0
          · subst hy
            wp_auto
            rm_tail r0
          · rw [decide_eq_false hy]
            wp_auto
            iapply IH $$ %r0 Hp Hst Hperm Hg Hrr HΦ
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
          wp_apply os.model.wp_removeAllFrom_leaf (child d b) c R J (DFrac.own ε) (DFrac.own 1)
            (hJ'.restrict J (.only [c])) q hcN
            (fun J' h' => by
              rw [os.restrict_only_cur] at h'
              obtain ⟨i, hi⟩ := hfo c _ (hsubk c _ h')
              cases hi) (.inl rfl) $$ [Hpc Hc Hperm] as %pe ⟨Hpc, Hperm, Hpe, %hc', Hc, %hlo⟩
          · iframe; iframe #
          imod os.osNames_merge1 R J c hc' (hJ'.restrict J (.except [c])) $$ Hsi Hc Hr
            with ⟨%h'', HJ, %hm⟩
          have hsub'' : EntsSub h''.cur hJ0.cur := os.entsSub_merge1 hsubk hlo hm
          wp_apply os.model.wp_prefixPath pe b $$ Hpe as Hpe
          by_cases hrn : r0 = null
          · rw [decide_eq_true hrn]
            wp_auto
            rw [show W64 ((k0 : Nat) : Int) + W64 1 = W64 ((k0 + 1 : Nat) : Int) by word]
            iapply IHe $$ %(k0 + 1) %pe %h'' [] Hpe HJ Hsl Hcap Hg HΦ Hperm Hp2 Hpc Hback Hfd
            · ipureintro; exact ⟨by omega, hsub''⟩
          · rw [decide_eq_false hrn]
            wp_auto
            rw [show W64 ((k0 : Nat) : Int) + W64 1 = W64 ((k0 + 1 : Nat) : Int) by word]
            iapply IHe $$ %(k0 + 1) %r0 %h'' [] Hrr HJ Hsl Hcap Hg HΦ Hperm Hp2 Hpc Hback Hfd
            · ipureintro; exact ⟨by omega, hsub''⟩
      · obtain ⟨he, rfl⟩ := hv
        wp_auto
        by_cases he4 : e = W64 4
        · rw [decide_eq_true he4]
          wp_auto
          iapply IHr $$ %false %rs %rr0' %sl0 [] [Hfd] Hsl Hcap HJ Hg Hrr HΦ Hperm Hp2 Hpc Hback
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
          rm_restore hsub
          by_cases he2 : e = W64 2
          · rw [decide_eq_true he2]
            wp_auto
            iapply HΦ
            iframe
            iapply os.peOk_null
          rw [decide_eq_false he2]
          wp_auto
          wp_apply os.model.wp_pathErrorPtr_rd _ e he as %pe Hpe
          try wp_auto
          iapply HΦ
          iframe

end proof

end EtcdGrove
end Perennial
