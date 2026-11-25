/- Lean-first (no Rocq counterpart).

`MainAt.spec` proved: `dirFits` answers `Fs.DirFits r` (so every file path fits); the root's claim
split to the run's file names (`claims_of_names`, `FileNames.lean`'s `mvccfullNames`, which
`FilePaths(MainConfig(r/mvccfull))` lists under `r`: `filePaths_at`); the loop's invariant: the names
before the counter found empty, those from it on still to check (a claim on each); when every
`absent` answered `true`, the fresh database files made from the claims (`files_of_done`), then
`Run.spec`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.MainAt
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.dirFits
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.absent
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.MainConfig
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.FilePaths
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.FileNames

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull Fs

theorem mf_lt (k len : w64) (n : Nat) (h : sint.Z k < sint.Z len) (hn : n = sint.nat len)
    (hk0 : 0 ≤ sint.Z k) : sint.nat k < n := by
  subst hn; revert h hk0; word

theorem mf_succ (k len : w64) (hk0 : 0 ≤ sint.Z k) (h : sint.Z k < sint.Z len) :
    sint.nat (k + W64 1) = sint.nat k + 1 := by
  revert hk0 h; word

theorem mf_succ_nonneg (k len : w64) (hk0 : 0 ≤ sint.Z k) (h : sint.Z k < sint.Z len) :
    0 ≤ sint.Z (k + W64 1) := by
  revert hk0 h; word

theorem mf_end (k len : w64) (n : Nat) (h : ¬ sint.Z k < sint.Z len) (hk : sint.nat k ≤ n)
    (hn : n = sint.nat len) : sint.nat k = n := by
  subst hn; revert h hk; word

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

-- The kernel's check of this proof takes about 9 minutes (VM, 2026-11-24): `FilePaths`' slice `s ↦* …`
-- (its spec's `TypedPointsto` instance) is compared with the loop body's after each
-- `wp_load_slice_index` (reached through `IntoValTyped`), equal only after unfolding both. Without the
-- options: "(kernel) deterministic timeout". The slice's list is never written out here (the loop
-- invariant leaves `Hs` in the frame, the load takes it from `Hs`), which keeps that comparison to
-- the iteration's re-framing. A proof-perf candidate.
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem MainAt.wp_proof (wp_dirFits : dirFits.spec (GF := GF) (hG := hG))
    (wp_absent : absent.spec (GF := GF) (hG := hG))
    (wp_MainConfig : MainConfig.spec (GF := GF) (hG := hG))
    (wp_FilePaths : FilePaths.spec (GF := GF) (hG := hG))
    (wp_Run : Run.spec (GF := GF) (hG := hG)) :
    MainAt.spec (GF := GF) (hG := hG) := by
  intro _ _ _ _ _ _ r
  wp_start as ⟨Hroot, Htok, #Hvoff⟩
  try wp_auto
  wp_apply wp_dirFits as %fits %hfits
  cases fits with
  | false =>
    try wp_auto
    iapply HΦ; itrivial
  | true =>
    have hd : Fs.DirFits r := hfits.1 rfl
    have hok : ∀ b ∈ mvccfullNames, NameOk b ∧ Fs.PathFits (Fs.child r b) := fun b hb =>
      ⟨mvccfullNames_ok b hb, Fs.pathFits_of_dirFits hd (mvccfullNames_len b hb)⟩
    try wp_auto
    rw [show r ++ go!"/mvccfull" = Fs.child r go!"mvccfull" from rfl]
    wp_apply wp_MainConfig as %mx Hmix
    try wp_auto
    wp_apply (wp_FilePaths (mainConfigM (Fs.child r go!"mvccfull") mx)
      (by show sint.Z (W64 12000) < 2 ^ 63 - 1; decide)) as %s Hs
    rw [filePaths_at r mx]
    iunfold rootClaimF at Hroot
    icases Hroot with ⟨%R, %j0, %h0, %q, %hr, #Hinv, #Hsh, Hn, Hperm⟩
    imod claims_of_names (hG := hG) R j0 mvccfullNames [] h0 mvccfullNames_nodup
      (fun _ _ h => absurd h List.not_mem_nil) $$ Hsh Hn with Hcl
    imod Fs.osPathS_root (E := ⊤) (L := hG.goose_localGS) R r j0 (DFrac.own 1) hr
      (fun _ _ => CoPset.mem_full) $$ Hsh with Hpath
    ihave %Hsl := ownSlice_len _ _ _ $$ Hs
    -- the names, a variable from here on (12002 of them: never unfold them)
    generalize hN : mvccfullNames = names at hok Hsl ⊢
    rw [List.length_map] at Hsl
    try wp_auto
    ihave HI : (∃ (k : w64) (pv : GoString), "i" ∷ i_ptr ↦ k ∗ "p" ∷ p_ptr ↦ pv ∗
        "Hpath" ∷ osPathS (GF := GF) R r (DFrac.own 1) j0 ∗
        "Hperm" ∷ osCallPerm (GF := GF) (callKey R r) q ∗
        "Hdone" ∷ ([∗list] b ∈ names.take (sint.nat k), ∃ hb : NamesH,
          osNames (GF := GF) j0 (.only [b]) (DFrac.own 1) hb ∗ ⌜hb.cur !! b = none⌝) ∗
        "Htodo" ∷ ([∗list] b ∈ names.drop (sint.nat k), ∃ hb : NamesH,
          osNames (GF := GF) j0 (.only [b]) (DFrac.own 1) hb) ∗
        "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ names.length⌝ : IProp GF)
      $$ [i p Hpath Hperm Hcl]
    · iexists W64 0, _
      rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero]
      iframe
      isplitl []
      · iapply BigSepL.bigSepL_nil.2; iempintro
      ipureintro; exact ⟨by decide, Nat.zero_le _⟩
    wp_for HI
    obtain ⟨Hk0, Hkl⟩ := Hk
    wp_if_destruct
    · -- an iteration: the name `names[k]`
      have hk : sint.nat k < names.length := mf_lt k s.len _ Hif Hsl.1 Hk0
      obtain ⟨b, hbl⟩ : ∃ b, names[sint.nat k]? = some b := ⟨_, List.getElem?_eq_getElem hk⟩
      have hpl : (names.map (Fs.child r))[sint.nat k]? = some (Fs.child r b) := by
        rw [List.getElem?_map, hbl]; rfl
      have hbm : b ∈ names := List.mem_of_getElem? hbl
      (try simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z s.len from ⟨Hk0, Hif⟩,
        _root_.and_self, ↓reduceIte])
      wp_apply wp_load_slice_index s (sint.Z k) _ (DFrac.own 1) _ Hk0 $$ [Hs] as Hs
      · iframe; ipureintro; exact hpl
      try wp_auto
      rw [List.drop_eq_getElem_cons hk, show names[sint.nat k] = b from
        (List.getElem?_eq_some_iff.1 hbl).2]
      icases BigSepL.bigSepL_cons.1 $$ Htodo with ⟨⟨%hb, Hb⟩, Htodo⟩
      wp_apply wp_absent r b R j0 1 hb q (hok b hbm).1 (fsNoErrAt_of_all (hok b hbm).2)
        $$ [Hpath Hb Hperm] as %res ⟨Hpath, Hb, Hperm, %hres⟩
      · iframe; iframe #
      have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := mf_succ k s.len Hk0 Hif
      cases res with
      | false =>
        try wp_auto
        wp_for_post
        iapply HΦ; itrivial
      | true =>
        try wp_auto
        wp_for_post
        iframe
        iexists k + W64 1, _
        iframe
        rw [hk1, List.take_succ, hbl, Option.toList_some]
        iframe Htodo
        isplitl [Hdone Hb]
        · iapply BigSepL.bigSepL_snoc.2
          iframe Hdone
          iexists hb
          iframe Hb
          ipureintro; exact hres rfl
        ipureintro; exact ⟨mf_succ_nonneg k s.len Hk0 Hif, by omega⟩
    · -- every name found empty: the run
      have hend : sint.nat k = names.length := mf_end k s.len _ Hif Hkl Hsl.1
      rw [hend, List.take_of_length_le (Nat.le_refl _)]
      imod files_of_done (hG := hG) R r j0 hr names q hok $$ Hinv Hsh Hdone Hperm with Hfiles
      try wp_auto
      wp_apply (wp_Run (mainConfigM (Fs.child r go!"mvccfull") mx)
          [W64 1, W64 1, W64 2, W64 1, W64 1, W64 0] (mainConfig_okAt _ mx) trivial trivial)
        $$ [Hfiles Htok Hmix] as %rep -
      · iframe Htok Hvoff
        iunfold mainMixOwn at Hmix
        icases Hmix with ⟨%Hp, Hs1, Ho, Hc, Hrr, Hrd, Ha, Hstt⟩
        isplitl [Hs1 Ho Hc Hrr Hrd Ha Hstt]
        · iunfold mixOwn
          simp only [mainConfigM]
          iexists DFrac.own 1, _, _, _, _, _, _
          iframe
        rw [filePaths_at r mx, hN, BigSepL.bigSepL_map]
        have heq : ∀ p, backend.fileHolds (GF := GF) p ∅ = backend.fileHoldsF p ∅ := fun p => by
          unfold backend.fileHolds; exact backend.onFs_eq _
        simp only [heq]
        iexact Hfiles
      (try wp_auto)
      iapply HΦ
      itrivial

end proof

end mvccfull
end EtcdGrove
end Perennial
