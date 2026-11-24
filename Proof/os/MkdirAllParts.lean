/-
The pieces of `os.MkdirAll`'s model (`TrustedCode/os.lean`) in the tree's shared mode, for
`Proof/os/MkdirAll.lean` (`notes/wal-fsext-i2-design.md`, "Implementation log, `os.MkdirAll`").
Lean-first; untrusted.

(`os.parentModel`, `os.model.wp_mkdirAllParent`: `PathParent.lean`.)
-/
module

public import Proof.os.PathKindS
public import Proof.os.StatS
public import Proof.os.PathParent
public import Proof.os.MkdirParts
public import Proof.os.StatAboveS
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

/-- Two fractions have a common part. -/
theorem os.qp_common (a b : Qp) : ∃ e a' b' : Qp, e + a' = a ∧ e + b' = b := by
  have ha := a.2
  have hb := b.2
  let e : Qp := (if a.val ≤ b.val then a else b).half
  have hea : e < a := by
    simp only [Qp.lt_iff, e, Qp.val_half]
    by_cases h : a.val ≤ b.val <;> simp only [h, ↓reduceIte] <;> grind
  have heb : e < b := by
    simp only [Qp.lt_iff, e, Qp.val_half]
    by_cases h : a.val ≤ b.val <;> simp only [h, ↓reduceIte] <;> grind
  obtain ⟨a', ha'⟩ := Qp.lt_iff_exists_add.mp hea
  obtain ⟨b', hb'⟩ := Qp.lt_iff_exists_add.mp heb
  exact ⟨e, a', b', ha', hb'⟩

/-- A root of well-formed roots is not strictly below a root. -/
theorem os.not_treeName_root {R : Roots} (hR : RootsOk R) {r : GoString} {j0 : Ino} (hm : (r, j0) ∈ R) :
    ¬ RootsTreeName R r := by
  rintro ⟨r', hr', cs, hne, -, hp⟩
  have hu : IsUnder r'.1 r := by
    rcases cs with _ | ⟨c, cs⟩
    · exact absurd rfl hne
    · right; exact ⟨c ++ cs.flatMap (slashB :: ·), by rw [hp]; simp [joinPath]⟩
  by_cases he : r'.1 = r
  · have hl := congrArg List.length hp
    rw [he] at hl
    rcases cs with _ | ⟨c, cs⟩
    · exact hne rfl
    · simp [joinPath] at hl
  · exact (hR.2.2 r' hr').2 (r, j0) hm he hu

/-- A path of a root and components, at least one, is strictly below the root. -/
theorem os.treeName_snoc {R : Roots} {r : GoString} {j0 : Ino} (hm : (r, j0) ∈ R)
    {cs : List GoString} {c : GoString} (hcs : ∀ x ∈ cs ++ [c], NameOk x) :
    RootsTreeName R (joinPath r (cs ++ [c])) :=
  ⟨(r, j0), hm, cs ++ [c], by simp, hcs, rfl⟩

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- A spine ends with its last component's claim. -/
theorem os.osSpine_unsnoc (cs : List GoString) (c : GoString) (j0 : Ino) (dq : DFrac) (J : Ino) :
    osSpine (GF := GF) j0 (cs ++ [c]) dq J ⊢ ∃ (j : Ino) (h : NamesH), osSpine j0 cs dq j ∗
      osNames j (.only [c]) dq h ∗ ⌜h.cur !! c = some (.dir J)⌝ := by
  induction cs generalizing j0 with
  | nil =>
    rw [List.nil_append, osSpine_cons]
    iintro ⟨%h, %J', Hn, %hJ, Hs⟩
    isimp only [osSpine_nil] at Hs
    icases Hs with %he
    subst he
    iexists j0, h
    rw [osSpine_nil]
    iframe
    isplitl [] <;> ipureintro
    · rfl
    · exact hJ
  | cons x cs ih =>
    rw [List.cons_append, osSpine_cons]
    iintro ⟨%h, %J', Hn, %hJ, Hs⟩
    icases ih J' $$ Hs with ⟨%j, %h', Hs, Hn', %hc⟩
    iexists j, h'
    rw [osSpine_cons]
    iframe
    isplitl [] <;> ipureintro
    · exact hJ
    · exact hc

/-- The path of a root and components is held by the spine of the components. -/
theorem os.osPathS_joinPath (R : Roots) (r : GoString) (j0 : Ino) (cs : List GoString) (dq : DFrac)
    (J : Ino) (hR : RootsOk R) (hm : (r, j0) ∈ R) (hcs : ∀ c ∈ cs, NameOk c) :
    osPathS (GF := GF) R (joinPath r cs) dq J ⊣⊢ osSpine j0 cs dq J := by
  unfold osPathS
  constructor
  · iintro ⟨%r', %j0', %cs', %hp, Hs⟩
    obtain ⟨-, hm', hcs', he⟩ := hp
    obtain ⟨hrj, rfl⟩ := root_split_unique hR hm hm' hcs hcs' he
    simp only [Prod.mk.injEq] at hrj
    obtain ⟨rfl, rfl⟩ := hrj
    iexact Hs
  · iintro Hs
    iexists r, j0, cs
    iframe
    ipureintro; exact ⟨hR, hm, hcs, rfl⟩

/-- A spine to `d/b` and a spine to `d` give back a whole spine to `d` and the claim on `b`. -/
theorem os.osPathS_unchild (R : Roots) (d b : GoString) (j J : Ino) (e a : Qp) (hb : NameOk b) :
    osPathS (GF := GF) R (child d b) (DFrac.own e) J ∗ osPathS R d (DFrac.own a) j ⊢
      ∃ h, osPathS R d (DFrac.own (e + a)) j ∗ osNames j (.only [b]) (DFrac.own e) h ∗
        ⌜h.cur !! b = some (.dir J)⌝ := by
  unfold osPathS
  iintro ⟨⟨%r, %j0, %cs, %hp, Hs⟩, ⟨%r', %j0', %cs', %hp', Hs'⟩⟩
  obtain ⟨hR, hm, hcs, he⟩ := hp
  obtain ⟨-, hm', hcs', rfl⟩ := hp'
  rw [← joinPath_snoc] at he
  have hcsb : ∀ x ∈ cs' ++ [b], NameOk x := by
    intro x hx; simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact hcs' x hx
    · exact hb
  obtain ⟨hrj, rfl⟩ := root_split_unique hR hm' hm hcsb hcs he
  simp only [Prod.mk.injEq] at hrj
  obtain ⟨rfl, rfl⟩ := hrj
  icases os.osSpine_unsnoc cs' b j0' (DFrac.own e) J $$ Hs with ⟨%j'', %h, Hs, Hn, %hJ⟩
  icases osSpine_join cs' j0' e a j'' j $$ [Hs Hs'] with ⟨%hj, Hs⟩
  · isplitl [Hs]; iexact Hs; iexact Hs'
  subst hj
  iexists h
  isplitl [Hs]
  · iexists _, _, cs'
    iframe
    ipureintro; exact ⟨hR, hm', hcs', rfl⟩
  iframe
  ipureintro; exact hJ

-- `os.Mkdir.wp_takenS` is in `MkdirParts.lean` (over Go's `os.Mkdir`, 2026-11-24). Go's `MkdirAll`
-- recurses through the strict ancestors of a root, each a `Stat` (`modelStatAbove`), a `Mkdir`
-- (`os.Mkdir.wp_notTree`) and an `Lstat`: `os.MkdirAll.wp_aboveS`, by strong induction on the
-- path's length (`os.rootsAbove_parent`).

set_option hygiene false in
/-- `IsDir` through the `FileInfo` of a `*fileStat` (`os.ownFileStat` in `H`): some boolean. -/
local macro "fileStat_isDir" H:ident : tactic => `(tactic| (
  unfold os.ownFileStat
  icases $H:ident with ⟨#Hsz, ⟨%mode, #Hmode⟩, -⟩
  wp_method_call
  wp_call
  try wp_auto
  wp_method_call
  wp_call
  try wp_auto
  haveI : go.NotInterface go.uint32 := ⟨trivial⟩
  try wp_auto
  wp_method_call
  wp_call
  try wp_auto
  iclear Hsz Hmode))

/-- A strict ancestor of a root is not empty. -/
theorem os.rootsAbove_ne_nil {R : Roots} {p : GoString} (h : RootsAbove R p) : p ≠ [] := by
  rcases h with rfl | ⟨hne, -⟩
  · simp
  · exact hne

/-- `PathKind` of a strict ancestor of a root, as `os.Mkdir.wp_notTree` asks it. -/
theorem os.pathKind_above_notTree (R : Roots) (p : GoString) (hp : RootsAbove R p)
    (Φ : val → IProp GF) :
    osInv (GF := GF) ∗ osSharedInv R ∗ (∀ k : w64, ⌜k ≠ W64 1⌝ -∗ Φ #k) ⊢
      WP (App (Val (@! syscall.fsPathKind)) (Val #p)) {{ Φ }} := by
  iintro ⟨#Hos, #Hsi, HΦ⟩
  wp_stub syscall.fsPathKind.impl
  wp_apply wp_osPathKindAboveS R p hp CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi
  iapply HΦ
  ipureintro; decide

/-- `PathKind` of a root, as `os.Mkdir.wp_notTree` asks it. -/
theorem os.pathKind_root_notTree (R : Roots) (r : GoString) (j0 : Ino) (hR : RootsOk R)
    (hm : (r, j0) ∈ R) (Φ : val → IProp GF) :
    osInv (GF := GF) ∗ osSharedInv R ∗ (∀ k : w64, ⌜k ≠ W64 1⌝ -∗ Φ #k) ⊢
      WP (App (Val (@! syscall.fsPathKind)) (Val #r)) {{ Φ }} := by
  iintro ⟨#Hos, #Hsi, HΦ⟩
  wp_stub syscall.fsPathKind.impl
  wp_apply wp_osPathKindS R r ⟨r, j0, [], hm, by simp, by simp [joinPath]⟩
    CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi as %k %hk
  rcases hk with ⟨hk, -⟩ | ⟨-, rfl⟩
  · exact absurd hk (os.not_treeName_root hR hm)
  iapply HΦ
  ipureintro; decide

set_option hygiene false in
/-- The end of `MkdirAll(p)` at a strict ancestor `p` of a root (`hp`), after its parent: `Mkdir`
(`os.Mkdir.wp_notTree`: an error), `Lstat`, `IsDir`. -/
local macro "mkdirall_above_tail" : tactic => `(tactic| (
  wp_apply (os.Mkdir.wp_notTree R p perm (os.pathKind_above_notTree R p hp)) $$ [] as %e %he
  · isplitl [] <;> iassumption
  cases e with
  | nil => exact absurd rfl he
  | ok ie3 =>
  try wp_auto
  wp_apply os.Lstat.wp_aboveS p R hp $$ [] as %fi2 %err2 Hres2
  · isplitl [] <;> iassumption
  icases Hres2 with (⟨%fs2, %sz2, %hfe2, Hfs2⟩ | %herr2)
  · obtain ⟨rfl, rfl⟩ := hfe2
    try wp_auto
    fileStat_isDir Hfs2
    wp_if_destruct
    all_goals
      try wp_auto
      iapply HΦ
      try itrivial
  · cases err2 with
    | nil => exact absurd rfl herr2
    | ok ie4 =>
      try wp_auto
      iapply HΦ
      try itrivial))

/-- **`os.MkdirAll` of a strict ancestor of a root**: some error or `nil`, nothing changes (the
`Stat`s and `Lstat`s take no step, the `Mkdir`s fail). -/
theorem os.MkdirAll.wp_aboveS (p : GoString) (perm : w32) (R : Roots) (hp : RootsAbove R p) :
    {{ osInv (GF := GF) ∗ osSharedInv R }}
      (App (App (Val (@! os.MkdirAll)) (Val #p)) (Val #perm))
    {{ (err : GoInterface), RET #err; True }} := by
  suffices hsuf : ∀ (n : Nat) (p : GoString), p.length ≤ n → RootsAbove R p →
      {{ osInv (GF := GF) ∗ osSharedInv R }}
        (App (App (Val (@! os.MkdirAll)) (Val #p)) (Val #perm))
      {{ (err : GoInterface), RET #err; True }} from hsuf _ p (Nat.le_refl _) hp
  intro n
  induction n with
  | zero =>
    intro p hn hp
    exact absurd (List.eq_nil_of_length_eq_zero (by omega)) (os.rootsAbove_ne_nil hp)
  | succ n ih =>
  intro p hn hp
  have hpl := os.parentModel_length p (os.rootsAbove_ne_nil hp)
  wp_start as ⟨#Hos, #Hsi⟩
  try wp_auto
  wp_apply os.Stat.wp_aboveS p R hp $$ [] as %fi %err Hres
  · isplitl [] <;> iassumption
  icases Hres with (⟨%fs, %sz, %hfe, Hfs⟩ | %herr)
  · obtain ⟨rfl, rfl⟩ := hfe
    try wp_auto
    fileStat_isDir Hfs
    wp_if_destruct
    all_goals
      try wp_auto
      try wp_alloc pe as Hpe
      try wp_auto
      iapply HΦ
      try itrivial
  cases err with
  | nil => exact absurd rfl herr
  | ok ie =>
  try wp_auto
  mkdirall_parent p (
    try wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    try wp_auto
    wp_apply filepathlite.VolumeName.wp_lex
    try wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    try wp_auto
    by_cases hpe : os.parentModel p = []
    · rw [decide_eq_false (show ¬ (sint.Z (W64 (([] : GoString).length : Int)) <
          sint.Z (W64 ((os.parentModel p).length : Int))) by rw [hpe]; exact Int.lt_irrefl _)]
      try wp_auto
      mkdirall_above_tail
    · have hpos : 0 < (os.parentModel p).length := List.length_pos_iff.mpr hpe
      have hpb : (os.parentModel p).length < 2 ^ 63 := by omega
      rw [decide_eq_true (show sint.Z (W64 (([] : GoString).length : Int)) <
          sint.Z (W64 ((os.parentModel p).length : Int)) by simp only [List.length_nil]; word)]
      try wp_auto
      wp_apply (ih (os.parentModel p) (by omega) (os.rootsAbove_parent (.inl hp) hpe)) $$ []
        as %e -
      · isplitl [] <;> iassumption
      cases e with
      | ok ie2 =>
        try wp_auto
        iapply HΦ
        try itrivial
      | nil =>
        try wp_auto
        mkdirall_above_tail)

set_option hygiene false in
/-- The end of `MkdirAll(r)` at the root `r` (a spine `Hp`, `hPS`), after its parent: `Mkdir`
(`os.Mkdir.wp_notTree`: an error), `Lstat`, `IsDir`. -/
local macro "mkdirall_root_tail" : tactic => `(tactic| (
  wp_apply (os.Mkdir.wp_notTree R r perm (os.pathKind_root_notTree R r j0 hR hm)) $$ [] as %e %he
  · isplitl [] <;> iassumption
  cases e with
  | nil => exact absurd rfl he
  | ok ie3 =>
  try wp_auto
  wp_apply os.Lstat.wp_dirS r R J dq qc $$ [Hp Hperm] as %fi2 %err2 ⟨Hp, Hperm, Hres2⟩
  · iframe; iframe #
  ihave Hs := hPS.1 $$ Hp
  icases Hres2 with (⟨%fs2, %sz2, %hfe2, Hfs2⟩ | %herr2)
  · obtain ⟨rfl, rfl⟩ := hfe2
    try wp_auto
    fileStat_isDir Hfs2
    wp_if_destruct
    all_goals
      try wp_auto
      iapply HΦ
      iframe
  · cases err2 with
    | nil => exact absurd rfl herr2
    | ok ie4 =>
      try wp_auto
      iapply HΦ
      iframe))

/-- **`os.MkdirAll` of an existing directory** (a root and a spine of components to it), with a
fraction of the call permission: `nil` or an error, nothing changes. -/
theorem os.MkdirAll.wp_spineS (r : GoString) (j0 : Ino) (perm : w32) (R : Roots) (dq : DFrac)
    (qc : Qp) (hR : RootsOk R) (hm : (r, j0) ∈ R) (cs : List GoString) (J : Ino)
    (hcs : ∀ c ∈ cs, NameOk c) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osSpine j0 cs dq J ∗ osCallPerm (callKey R r) qc }}
      (App (App (Val (@! os.MkdirAll)) (Val #(joinPath r cs))) (Val #perm))
    {{ (err : GoInterface), RET #err; osSpine j0 cs dq J ∗ osCallPerm (callKey R r) qc }} := by
  obtain ⟨rcs, rfl⟩ : ∃ rcs, cs = rcs.reverse := ⟨cs.reverse, by simp⟩
  induction rcs generalizing J with
  | nil =>
    have hr0 : joinPath r [] = r := by simp [joinPath]
    have hPS := os.osPathS_joinPath (GF := GF) R r j0 [] dq J hR hm (by simp)
    rw [hr0] at hPS
    simp only [List.reverse_nil, hr0]
    have hrne : r ≠ [] := by
      obtain ⟨rc, hne, -, hrf⟩ := (hR.2.2 (r, j0) hm).1
      rcases rc with _ | ⟨x, rc⟩
      · exact absurd rfl hne
      · simp only at hrf; rw [hrf]; simp [joinPath]
    have hpl := os.parentModel_length r hrne
    wp_start as ⟨#Hos, #Hsi, Hs, Hperm⟩
    try wp_auto
    ihave Hp := hPS.2 $$ Hs
    wp_apply os.Stat.wp_dirS r R J dq qc $$ [Hp Hperm] as %fi %err ⟨Hp, Hperm, Hres⟩
    · iframe; iframe #
    icases Hres with (⟨%fs, %sz, %hfe, Hfs⟩ | %herr)
    · obtain ⟨rfl, rfl⟩ := hfe
      try wp_auto
      fileStat_isDir Hfs
      ihave Hs := hPS.1 $$ Hp
      wp_if_destruct
      all_goals
        try wp_auto
        try wp_alloc pe as Hpe
        try wp_auto
        iapply HΦ
        iframe
    cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    try wp_auto
    mkdirall_parent r (
      try wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
      try wp_auto
      wp_apply filepathlite.VolumeName.wp_lex
      try wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
      try wp_auto
      by_cases hpe : os.parentModel r = []
      · rw [decide_eq_false (show ¬ (sint.Z (W64 (([] : GoString).length : Int)) <
            sint.Z (W64 ((os.parentModel r).length : Int))) by rw [hpe]; exact Int.lt_irrefl _)]
        try wp_auto
        mkdirall_root_tail
      · have hpos : 0 < (os.parentModel r).length := List.length_pos_iff.mpr hpe
        have hpb : (os.parentModel r).length < 2 ^ 63 := by omega
        rw [decide_eq_true (show sint.Z (W64 (([] : GoString).length : Int)) <
            sint.Z (W64 ((os.parentModel r).length : Int)) by simp only [List.length_nil]; word)]
        try wp_auto
        wp_apply (os.MkdirAll.wp_aboveS (os.parentModel r) perm R
          (os.rootsAbove_parent (.inr ⟨(r, j0), hm, rfl⟩) hpe)) $$ [] as %e -
        · isplitl [] <;> iassumption
        cases e with
        | ok ie2 =>
          try wp_auto
          ihave Hs := hPS.1 $$ Hp
          iapply HΦ
          iframe
        | nil =>
          try wp_auto
          mkdirall_root_tail)
  | cons c rcs ih =>
    rw [List.reverse_cons] at hcs ⊢
    have hcs' : ∀ x ∈ rcs.reverse, NameOk x := fun x hx => hcs x (by simp at hx ⊢; exact .inl hx)
    have ih' := fun J => ih J hcs'
    clear ih
    have hc : NameOk c := hcs c (by simp)
    have hpar : os.parentModel (joinPath r (rcs.reverse ++ [c])) = joinPath r rcs.reverse :=
      os.parentModel_joinPath_snoc r rcs.reverse c hc
    have hPne : joinPath r (rcs.reverse ++ [c]) ≠ [] := by
      rw [joinPath_snoc]; simp [child]
    have hpl := os.parentModel_length _ hPne
    rw [hpar] at hpl
    have hrne : 0 < r.length := by
      obtain ⟨rc, hne, -, hrf⟩ := (hR.2.2 (r, j0) hm).1
      rcases rc with _ | ⟨x, rc⟩
      · exact absurd rfl hne
      · simp only at hrf; rw [hrf]; simp [joinPath]
    have hplen : 0 < (joinPath r rcs.reverse).length := by
      simp only [joinPath, List.length_append]; omega
    wp_start as ⟨#Hos, #Hsi, Hs, Hperm⟩
    try wp_auto
    ihave Hp := (os.osPathS_joinPath R r j0 _ dq J hR hm hcs).2 $$ Hs
    ihave Hperm := osCallPerm_congr _ (callKey_joinPath hR hm (rcs.reverse ++ [c])).symm $$ Hperm
    wp_apply os.Stat.wp_dirS $$ [Hp Hperm] as %fi %err ⟨Hp, Hperm, Hres⟩
    · iframe; iframe #
    ihave Hperm := osCallPerm_congr _ (callKey_joinPath hR hm (rcs.reverse ++ [c])) $$ Hperm
    icases Hres with (⟨%fs, %sz, %hfe, Hfs⟩ | %herr)
    · obtain ⟨rfl, rfl⟩ := hfe
      try wp_auto
      fileStat_isDir Hfs
      ihave Hs := (os.osPathS_joinPath R r j0 _ dq J hR hm hcs).1 $$ Hp
      wp_if_destruct
      all_goals
        try wp_auto
        try wp_alloc pe as Hpe
        try wp_auto
        iapply HΦ
        iframe
    cases err with
    | nil => exact absurd rfl herr
    | ok ie =>
    try wp_auto
    mkdirall_parent (joinPath r (rcs.reverse ++ [c])) (
      rw [hpar]
      try wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
      try wp_auto
      wp_apply filepathlite.VolumeName.wp_lex
      try wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
      try wp_auto
      have hpb : (joinPath r rcs.reverse).length < 2 ^ 63 := by omega
      rw [decide_eq_true (show sint.Z (W64 (([] : GoString).length : Int)) <
          sint.Z (W64 ((joinPath r rcs.reverse).length : Int)) by simp only [List.length_nil]; word)]
      try wp_auto
      ihave Hs := (os.osPathS_joinPath R r j0 _ dq J hR hm hcs).1 $$ Hp
      icases os.osSpine_unsnoc _ c j0 dq J $$ Hs with ⟨%j, %h, Hs, Hn, %hJ⟩
      wp_apply (ih' j) $$ [Hs Hperm] as %e ⟨Hs, Hperm⟩
      · iframe; iframe #
      cases e with
      | ok ie =>
        try wp_auto
        iapply HΦ
        iframe
        iapply osSpine_snoc _ j0 dq j c h J hJ $$ Hs Hn
      | nil =>
      try wp_auto
      have hPS := os.osPathS_joinPath (GF := GF) R r j0 (rcs.reverse ++ [c]) dq J hR hm hcs
      rw [joinPath_snoc] at hPS ⊢
      ihave Hp := (os.osPathS_joinPath R r j0 _ dq j hR hm hcs').2 $$ Hs
      ihave Hperm := osCallPerm_congr _ (callKey_joinPath hR hm rcs.reverse).symm $$ Hperm
      wp_apply os.Mkdir.wp_takenS (joinPath r rcs.reverse) c perm R j (.only [c]) dq dq h qc hc
        (by simp [NameSet.Mem]) (by rw [hJ]; rfl) $$ [Hp Hn Hperm] as %e ⟨Hp, Hn, Hperm, %he⟩
      · iframe; iframe #
      cases e with
      | nil => exact absurd rfl he
      | ok ie =>
      try wp_auto
      ihave Hpc := osPathS_child R _ c dq j J h hc hJ $$ Hp Hn
      have hkc : callKey R (child (joinPath r rcs.reverse) c) = callKey R (joinPath r rcs.reverse) := by
        rw [← joinPath_snoc, callKey_joinPath hR hm, callKey_joinPath hR hm]
      ihave Hperm := osCallPerm_congr _ hkc.symm $$ Hperm
      wp_apply os.Lstat.wp_dirS $$ [Hpc Hperm] as %fi %err ⟨Hpc, Hperm, Hres⟩
      · iframe; iframe #
      ihave Hperm := osCallPerm_congr _ (hkc.trans (callKey_joinPath hR hm rcs.reverse)) $$ Hperm
      ihave Hs := hPS.1 $$ Hpc
      icases Hres with (⟨%fs, %sz, %hfe, Hfs⟩ | %herr)
      · obtain ⟨rfl, rfl⟩ := hfe
        try wp_auto
        fileStat_isDir Hfs
        wp_if_destruct
        all_goals
          try wp_auto
          iapply HΦ
          iframe
      · cases err with
        | nil => exact absurd rfl herr
        | ok ie' =>
        try wp_auto
        iapply HΦ; iframe)

end proof

end EtcdGrove
end Perennial
