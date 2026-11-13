/-
The pieces of `os.MkdirAll`'s model (`TrustedCode/os.lean`) in the tree's shared mode, for
`Proof/os/MkdirAll.lean` (`notes/wal-fsext-i2-design.md`, "Implementation log, `os.MkdirAll`").
Lean-first; untrusted.

* `os.parentModel`, `os.model.wp_mkdirAllParent`: `MkdirAll`'s `parent` of any path, and
  `os.parentModel_child`: of `d/b` it is `d`.
-/
module

public import LinuxFs.Proof.os.PathKindS
public import LinuxFs.Proof.os.StatS
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

/-- `MkdirAll`'s first loop, on the length `n` of the prefix left (`i = n - 1`): skip trailing
separators. -/
def os.trailIdx (p : GoString) : Nat → Nat
  | 0 => 0
  | n + 1 => if p.getD n 0 = slashB then os.trailIdx p n else n + 1

/-- `MkdirAll`'s second loop: skip the last component. -/
def os.backIdx (p : GoString) : Nat → Nat
  | 0 => 0
  | n + 1 => if p.getD n 0 = slashB then n + 1 else os.backIdx p n

/-- `MkdirAll`'s `parent` of `p`: up to the last separator before its last component. -/
def os.parentModel (p : GoString) : GoString := p.take (os.backIdx p (os.trailIdx p p.length) - 1)

theorem os.trailIdx_le (p : GoString) (n : Nat) : os.trailIdx p n ≤ n := by
  induction n with
  | zero => simp [os.trailIdx]
  | succ n ih => simp only [os.trailIdx]; split <;> omega

theorem os.backIdx_le (p : GoString) (n : Nat) : os.backIdx p n ≤ n := by
  induction n with
  | zero => simp [os.backIdx]
  | succ n ih => simp only [os.backIdx]; split <;> omega

theorem os.backIdx_child (d b : GoString) (hb : slashB ∉ b) :
    ∀ k ≤ b.length, os.backIdx (child d b) (d.length + 1 + k) = d.length + 1 := by
  intro k
  induction k with
  | zero =>
    intro _
    show os.backIdx (child d b) (d.length + 1) = d.length + 1
    simp [os.backIdx, child, List.getD_eq_getElem?_getD]
  | succ k ih =>
    intro hk
    rw [show d.length + 1 + (k + 1) = (d.length + 1 + k) + 1 by omega]
    simp only [os.backIdx]
    have hkb : k < b.length := by omega
    have hg : (child d b).getD (d.length + 1 + k) 0 = b[k] := by
      simp [child, List.getD_eq_getElem?_getD, List.getElem?_append_right,
        show d.length ≤ d.length + 1 + k by omega, show d.length + 1 + k - d.length = k + 1 by omega,
        List.getElem?_eq_getElem hkb]
    have hne : b[k] ≠ slashB := fun h => hb (h ▸ List.getElem_mem hkb)
    simp only [hg, hne, ↓reduceIte]
    exact ih (by omega)

theorem os.parentModel_child (d b : GoString) (hb : NameOk b) : os.parentModel (child d b) = d := by
  obtain ⟨hne, -, -, hs, -⟩ := hb
  have hlen : (child d b).length = d.length + 1 + b.length := by simp [child]; omega
  obtain ⟨k, hk⟩ : ∃ k, b.length = k + 1 := ⟨b.length - 1, by
    cases b with | nil => exact absurd rfl hne | cons _ _ => simp⟩
  have ht : os.trailIdx (child d b) (child d b).length = (child d b).length := by
    rw [hlen, hk, show d.length + 1 + (k + 1) = (d.length + 1 + k) + 1 by omega]
    simp only [os.trailIdx]
    have hkb : k < b.length := by omega
    have hg : (child d b).getD (d.length + 1 + k) 0 = b[k] := by
      simp [child, List.getD_eq_getElem?_getD, List.getElem?_append_right,
        show d.length ≤ d.length + 1 + k by omega, show d.length + 1 + k - d.length = k + 1 by omega,
        List.getElem?_eq_getElem hkb]
    have hne : b[k] ≠ slashB := fun h => hs (h ▸ List.getElem_mem hkb)
    simp only [hg, hne, ↓reduceIte]
  unfold os.parentModel
  rw [ht, hlen, os.backIdx_child d b hs b.length (Nat.le_refl _)]
  simp [child]

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
variable [os.Assumptions] [os.fileStat.FieldAssumptions]

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

/-- `os.Mkdir(d/b)` of a name holding something (a fraction of a claim on names containing `b`), with
a fraction of the call permission: an error, no effect. -/
theorem os.Mkdir.wp_takenS (d b : GoString) (perm : w32) (R : Roots) (j : Ino) (N : NameSet)
    (dq dqn : DFrac) (h : NamesH) (qc : Qp) (hb : NameOk b) (hN : N.Mem b)
    (hi : (h.cur !! b).isSome) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d dq j ∗ osNames j N dqn h ∗ osCallPerm qc }}
      (App (App (Val (@! os.Mkdir)) (Val #(child d b))) (Val #perm))
    {{ (err : GoInterface), RET #err; osPathS R d dq j ∗ osNames j N dqn h ∗ osCallPerm qc ∗
        ⌜err ≠ interface.nil⌝ }} := by
  wp_start as ⟨#Hos, #Hsi, Hp, Hn, Hperm⟩
  imod osLogLb_0 with #Hlb
  iloeb as IH generalizing Hperm Hp Hn HΦ
  wp_apply +noauto wp_osCallBeginS R qc 0 CoPset.subseteq_top CoPset.subseteq_top
    $$ Hos Hsi Hperm Hlb as %t %s0 %hs Hk Hls
  iclear Hls
  wp_apply +noauto wp_osMkdirS_some R d b j N dq dqn h t s0 qc hb hN hi
    CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi Hp Hn Hk as %e %he Hperm Hp Hn
  wp_auto
  by_cases he4 : e = W64 4
  · rw [decide_eq_true he4]
    wp_auto
    iapply IH $$ Hperm Hp Hn HΦ
  rw [decide_eq_false (show e ≠ W64 4 from he4)]
  wp_auto
  rw [decide_eq_false (show e ≠ W64 0 from he)]
  wp_auto
  unfold os.model.pathError
  wp_apply wp_errno
  iapply HΦ
  iframe
  ipureintro; intro hc; cases hc

/-- `os.IsPathSeparator(c)`: whether `c` is `'/'`. -/
theorem os.wp_IsPathSeparator (c : w8) :
    {{ (True : IProp GF) }} (App (Val #(functions go!"os.IsPathSeparator" [])) (Val #c))
    {{ RET #(decide (c = slashB)); True }} := by
  rw [show (go!"os.IsPathSeparator" : GoString) = os.IsPathSeparator from rfl]
  wp_start
  try wp_auto
  rw [show decide (W8 47 = c) = decide (c = slashB) from decide_eq_decide.mpr eq_comm]
  iapply HΦ
  try itrivial

/-- `MkdirAll`'s `parent` of any path: `os.parentModel`. -/
theorem os.model.wp_mkdirAllParent (p : GoString) :
    {{ (True : IProp GF) }} (App (Val os.model.mkdirAllParent) (Val #p))
    {{ RET #(os.parentModel p); True }} := by
  wp_start
  try unfold os.model.mkdirAllParent
  try wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %hlen
  obtain ⟨n, hn⟩ : ∃ n : Nat, n = p.length := ⟨_, rfl⟩
  rw [show W64 (p.length : Int) = W64 (n : Int) from by rw [hn]]
  have hT : os.trailIdx p n = os.trailIdx p p.length := by rw [hn]
  have Hn : n ≤ p.length := by omega
  clear hn
  try wp_auto
  iclear Hpre
  iloeb as IH generalizing %n %hT %Hn
  cases n with
  | zero =>
    simp only [show ¬ sint.Z (W64 0) ≤ sint.Z (W64 ((0 : Nat) : Int) - W64 1) by decide,
      _root_.decide_false]
    wp_auto
    have hM : os.parentModel p = List.take (0 - 0) (List.drop 0 p) := by
      unfold os.parentModel; rw [← hT]; simp [os.trailIdx, os.backIdx]
    rw [← hM]
    iapply HΦ
    itrivial
  | succ k =>
    rw [show W64 ((k + 1 : Nat) : Int) - W64 1 = W64 (k : Int) by word]
    simp only [show sint.Z (W64 0) ≤ sint.Z (W64 (k : Int)) by word, _root_.decide_true]
    wp_auto
    have hk : k < p.length := by omega
    simp only [show (0 : Int) ≤ sint.Z (W64 (k : Int)) by word, ↓reduceIte,
      show sint.nat (W64 (k : Int)) = k by word, List.getElem?_eq_getElem hk]
    try wp_auto
    wp_apply os.wp_IsPathSeparator
    by_cases hs : p[k] = slashB
    · rw [decide_eq_true hs]
      wp_auto
      have hT' : os.trailIdx p k = os.trailIdx p p.length := by
        rw [← hT]; simp only [os.trailIdx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
          Option.getD_some, hs, ↓reduceIte]
      iapply IH $$ %k %hT' %(by omega) HΦ
    · rw [decide_eq_false hs]
      wp_auto
      have hT1 : os.trailIdx p (k + 1) = k + 1 := by
        simp only [os.trailIdx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
          Option.getD_some, hs, ↓reduceIte]
      have hB : os.backIdx p (k + 1) = os.backIdx p (os.trailIdx p p.length) := by
        rw [← hT, hT1]
      rw [show W64 (k : Int) = W64 ((k + 1 : Nat) : Int) - W64 1 by word]
      generalize k + 1 = m at hB Hn
      clear hT hT1 hk hs
      iclear IH
      iloeb as IH generalizing %m %hB %Hn
      cases m with
      | zero =>
        simp only [show ¬ sint.Z (W64 0) ≤ sint.Z (W64 ((0 : Nat) : Int) - W64 1) by decide,
          _root_.decide_false]
        wp_auto
        have hM : os.parentModel p = List.take (0 - 0) (List.drop 0 p) := by
          unfold os.parentModel; rw [← hB]; simp [os.backIdx]
        rw [← hM]
        iapply HΦ
        itrivial
      | succ k =>
        rw [show W64 ((k + 1 : Nat) : Int) - W64 1 = W64 (k : Int) by word]
        simp only [show sint.Z (W64 0) ≤ sint.Z (W64 (k : Int)) by word, _root_.decide_true]
        wp_auto
        have hk : k < p.length := by omega
        simp only [show (0 : Int) ≤ sint.Z (W64 (k : Int)) by word, ↓reduceIte,
          show sint.nat (W64 (k : Int)) = k by word, List.getElem?_eq_getElem hk]
        try wp_auto
        wp_apply os.wp_IsPathSeparator
        by_cases hs : p[k] = slashB
        · rw [decide_eq_true hs]
          wp_auto
          simp only [show ¬ sint.Z (W64 (k : Int)) < sint.Z (W64 0) by word, _root_.decide_false]
          wp_auto
          rw [ite_cond_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
          wp_auto
          have hM : os.parentModel p = List.take (sint.nat (W64 (k : Int)) - 0) (List.drop 0 p) := by
            unfold os.parentModel
            rw [← hB]
            simp only [os.backIdx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
              Option.getD_some, hs, ↓reduceIte, List.drop_zero,
              show sint.nat (W64 (k : Int)) = k by word]
            rfl
          rw [← hM]
          iapply HΦ
          itrivial
        · rw [decide_eq_false hs]
          wp_auto
          have hB' : os.backIdx p k = os.backIdx p (os.trailIdx p p.length) := by
            rw [← hB]; simp only [os.backIdx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk,
              Option.getD_some, hs, ↓reduceIte]
          iapply IH $$ %k %hB' %(by omega) HΦ

set_option hygiene false in
/-- The end of `mkdirAllAbove`: `Lstat` sees a directory (`nil`), or `Mkdir`'s error. -/
local macro "above_tail" : tactic => `(tactic| (
  wp_apply wp_ArbitraryInt as %y _
  by_cases hy : y = W64 0
  · subst hy
    try wp_auto
    iapply HΦ $$ %_
    itrivial
  rw [decide_eq_false hy]
  try wp_auto
  wp_apply wp_ArbitraryInt as %m _
  try wp_auto
  unfold os.model.pathError
  by_cases hm : m = W64 0
  · subst hm
    try wp_auto
    wp_apply wp_errno
    try wp_auto
    iapply HΦ $$ %_
    itrivial
  · rw [decide_eq_false hm]
    try wp_auto
    wp_apply wp_errno
    try wp_auto
    iapply HΦ $$ %_
    itrivial))

/-- `MkdirAll` at a root or an ancestor of one, no extension step: `nil` or an error, any path. -/
theorem os.model.wp_mkdirAllAbove (p : GoString) :
    {{ (True : IProp GF) }} (App (Val os.model.mkdirAllAbove) (Val #p))
    {{ (err : GoInterface), RET #err; True }} := by
  wp_start
  iclear Hpre
  try unfold os.model.mkdirAllAbove
  try wp_auto
  iloeb as IH generalizing %p %Φ HΦ
  wp_apply wp_ArbitraryInt as %x _
  by_cases hx : x = W64 0
  · subst hx
    wp_auto
    iapply HΦ $$ %_
    itrivial
  rw [decide_eq_false hx]
  wp_auto
  wp_apply os.model.wp_mkdirAllParent
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  try wp_auto
  wp_if_destruct
  · wp_apply IH as %e _
    cases e with
    | ok i =>
      wp_auto
      iapply HΦ $$ %_
      itrivial
    | nil =>
      wp_auto
      above_tail
  · try wp_auto
    above_tail

set_option hygiene false in
/-- `IsDir` through the `FileInfo` of a `*fileStat` (`os.ownFileStat` in `H`): some boolean. -/
local macro "fileStat_isDir" H:ident : tactic => `(tactic| (
  unfold os.ownFileStat
  icases $H:ident with ⟨#Hsz, %mode, #Hmode⟩
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

/-- **`os.MkdirAll` of an existing directory** (a root and a spine of components to it), with a
fraction of the call permission: `nil` or an error, nothing changes. -/
theorem os.MkdirAll.wp_spineS (r : GoString) (j0 : Ino) (perm : w32) (R : Roots) (dq : DFrac)
    (qc : Qp) (hR : RootsOk R) (hm : (r, j0) ∈ R) (cs : List GoString) (J : Ino)
    (hcs : ∀ c ∈ cs, NameOk c) :
    {{ osInv (GF := GF) ∗ osSharedInv R ∗ osSpine j0 cs dq J ∗ osCallPerm qc }}
      (App (App (Val #(functions go!"os.MkdirAll" [])) (Val #(joinPath r cs))) (Val #perm))
    {{ (err : GoInterface), RET #err; osSpine j0 cs dq J ∗ osCallPerm qc }} := by
  obtain ⟨rcs, rfl⟩ : ∃ rcs, cs = rcs.reverse := ⟨cs.reverse, by simp⟩
  induction rcs generalizing J with
  | nil =>
    rw [show (go!"os.MkdirAll" : GoString) = os.MkdirAll from rfl]
    simp only [List.reverse_nil, show joinPath r [] = r by simp [joinPath]]
    wp_start as ⟨#Hos, #Hsi, Hs, Hperm⟩
    try wp_auto
    wp_apply wp_osPathKindS R r ⟨r, j0, [], hm, by simp, by simp [joinPath]⟩
      CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi as %k %hk
    rcases hk with ⟨hk, -⟩ | ⟨-, rfl⟩
    · exact absurd hk (os.not_treeName_root hR hm)
    wp_auto
    wp_apply os.model.wp_mkdirAllAbove as %e _
    iapply HΦ
    iframe
  | cons c rcs ih =>
    rw [List.reverse_cons] at hcs ⊢
    have hcs' : ∀ x ∈ rcs.reverse, NameOk x := fun x hx => hcs x (by simp at hx ⊢; exact .inl hx)
    have ih' := fun J => ih J hcs'
    clear ih
    rw [show (go!"os.MkdirAll" : GoString) = os.MkdirAll from rfl]
    wp_start as ⟨#Hos, #Hsi, Hs, Hperm⟩
    try wp_auto
    wp_apply wp_osPathKindS R _ ⟨r, j0, _, hm, hcs, rfl⟩
      CoPset.subseteq_top CoPset.subseteq_top $$ Hos Hsi as %k %hk
    obtain ⟨-, rfl⟩ := hk.resolve_right (fun h => h.1 (os.treeName_snoc hm hcs))
    wp_auto
    rw [show (go!"os.Stat" : GoString) = os.Stat from rfl]
    ihave Hp := (os.osPathS_joinPath R r j0 _ dq J hR hm hcs).2 $$ Hs
    wp_apply os.Stat.wp_dirS $$ [Hp Hperm] as %fi %err ⟨Hp, Hperm, Hres⟩
    · iframe; iframe #
    icases Hres with (⟨%fs, %sz, %hfe, Hfs⟩ | %herr)
    · obtain ⟨rfl, rfl⟩ := hfe
      wp_auto
      fileStat_isDir Hfs
      ihave Hs := (os.osPathS_joinPath R r j0 _ dq J hR hm hcs).1 $$ Hp
      wp_if_destruct
      · unfold os.model.pathError
        wp_apply wp_errno
        iapply HΦ; iframe
      · iapply HΦ; iframe
    · cases err with
      | nil => exact absurd rfl herr
      | ok ie =>
      wp_auto
      have hcs1 : ∀ x ∈ rcs.reverse ++ [c], NameOk x := hcs
      have hc : NameOk c := hcs c (by simp)
      have hpar : os.parentModel (joinPath r (rcs.reverse ++ [c])) = joinPath r rcs.reverse := by
        rw [joinPath_snoc]; exact os.parentModel_child _ c hc
      have hrne : 0 < r.length := by
        obtain ⟨rc, hne, -, hrf⟩ := (hR.2.2 (r, j0) hm).1
        rcases rc with _ | ⟨x, rc⟩
        · exact absurd rfl hne
        · simp only at hrf; rw [hrf]; simp [joinPath]
      have hplen : 0 < (joinPath r rcs.reverse).length := by
        simp only [joinPath, List.length_append]; omega
      wp_apply os.model.wp_mkdirAllParent
      rw [hpar]
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %hlen
      rw [decide_eq_true (show sint.Z (W64 0) < sint.Z (W64 ((joinPath r rcs.reverse).length : Int))
        by word)]
      wp_auto
      ihave Hs := (os.osPathS_joinPath R r j0 _ dq J hR hm hcs).1 $$ Hp
      icases os.osSpine_unsnoc _ c j0 dq J $$ Hs with ⟨%j, %h, Hs, Hn, %hJ⟩
      wp_apply (ih' j) $$ [Hs Hperm] as %e ⟨Hs, Hperm⟩
      · iframe; iframe #
      cases e with
      | ok ie =>
        wp_auto
        iapply HΦ
        iframe
        iapply osSpine_snoc _ j0 dq j c h J hJ $$ Hs Hn
      | nil =>
      wp_auto
      have hPS := os.osPathS_joinPath (GF := GF) R r j0 (rcs.reverse ++ [c]) dq J hR hm hcs
      rw [joinPath_snoc] at hPS ⊢
      rw [show (go!"os.Mkdir" : GoString) = os.Mkdir from rfl]
      ihave Hp := (os.osPathS_joinPath R r j0 _ dq j hR hm hcs').2 $$ Hs
      wp_apply os.Mkdir.wp_takenS (joinPath r rcs.reverse) c perm R j (.only [c]) dq dq h qc hc
        (by simp [NameSet.Mem]) (by rw [hJ]; rfl) $$ [Hp Hn Hperm] as %e ⟨Hp, Hn, Hperm, %he⟩
      · iframe; iframe #
      cases e with
      | nil => exact absurd rfl he
      | ok ie =>
      wp_auto
      rw [show (go!"os.Lstat" : GoString) = os.Lstat from rfl]
      ihave Hpc := osPathS_child R _ c dq j J h hc hJ $$ Hp Hn
      wp_apply os.Lstat.wp_dirS $$ [Hpc Hperm] as %fi %err ⟨Hpc, Hperm, Hres⟩
      · iframe; iframe #
      ihave Hs := hPS.1 $$ Hpc
      icases Hres with (⟨%fs, %sz, %hfe, Hfs⟩ | %herr)
      · obtain ⟨rfl, rfl⟩ := hfe
        wp_auto
        fileStat_isDir Hfs
        wp_if_destruct
        · iapply HΦ; iframe
        · iapply HΦ; iframe
      · cases err with
        | nil => exact absurd rfl herr
        | ok ie' =>
        wp_auto
        iapply HΦ; iframe

end proof

end EtcdGrove
end Perennial
