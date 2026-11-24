/-
Proof of `Spec/go_etcd_io/etcd/api/v3/version/Cluster.lean`: `version.Cluster(v)` over
`semver.NewVersion`'s spec (the trust boundary), `Version.Major`/`Minor`, Perennial's model of
`fmt.Sprintf` and `strings.Split` (a trust-boundary axiom until 2026-11-22, prove-ps2-client).
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.api.v3.version.Cluster
public import Spec.github_com.Masterminds.semver.v3.NewVersion
public import Spec.github_com.Masterminds.semver.v3.Version__Major
public import Spec.github_com.Masterminds.semver.v3.Version__Minor
public import Proof.fmt.OutLemmas
public import Perennial.Spec.strings.Split
public import Proof.unicode.utf8.Valid
public import Perennial.Proof.fmt.Link
public import Proof.fmt.SprintfPure

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section pure
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

theorem version.decimalNat_ascii (n : Nat) : asciiStr (_root_.Perennial.fmt.decimalNat n) := by
  intro c hc
  have := _root_.Perennial.fmt.decimalNat_digits n c hc
  have h2 : (uint.Z c : Int) = (c.toNat : Int) := by simp [uint.Z]
  omega

/-- `%d` of a `uint64` is ASCII. -/
theorem version.decimalPad0_ascii (a : w64) : asciiStr (_root_.Perennial.fmt.decimalPad 0 (uint.Z a)) := by
  rw [_root_.Perennial.fmt.decimalPad_zero, _root_.Perennial.fmt.decimal_of_nonneg (by word)]
  exact version.decimalNat_ascii _

/-- A field without a dot, then a dot: `strings.Split` ends the current field there. -/
theorem version.splitAux_dot (a rest f : GoString) (ha : (W8 46 : w8) ∉ a) :
    strings.splitAux go!"." (a ++ W8 46 :: rest) f = (f ++ a) :: strings.splitAux go!"." rest [] := by
  induction a generalizing f with
  | nil =>
    simp only [List.nil_append]
    rw [strings.splitAux]
    simp
  | cons c a ih =>
    simp only [List.mem_cons, not_or] at ha
    rw [List.cons_append, strings.splitAux]
    have hc : ¬ (go!"." ≠ [] ∧ go!"." <+: c :: (a ++ W8 46 :: rest)) := by
      rintro ⟨-, h⟩
      have : (go!"." : GoString) = [W8 46] := rfl
      rw [this, List.cons_prefix_cons] at h
      exact ha.1 h.1
    rw [ite_eq_right_of_eq_false _ _ (eq_false hc), ih _ ha.2]
    simp

theorem version.ascii_append {s t : GoString} (hs : asciiStr s) (ht : asciiStr t) :
    asciiStr (s ++ t) := by
  intro b hb
  rcases List.mem_append.1 hb with h | h
  · exact hs b h
  · exact ht b h

theorem version.splitAux_ne_nil (sep r f : GoString) : strings.splitAux sep r f ≠ [] := by
  fun_induction strings.splitAux sep r f <;> simp_all

theorem version.decDigits_noDot {a : GoString} (h : decDigits a) : (W8 46 : w8) ∉ a := by
  intro hm
  have := h.2 _ hm
  revert this; decide

theorem version.decDigits_ascii {a : GoString} (h : decDigits a) : asciiStr a := by
  intro c hc
  have := h.2 c hc
  omega

/-- The fields of a `semverStr`: its two numbers first. -/
theorem version.split_semverStr {v : GoString} (h : semverStr v) :
    ∃ a b r, strings.split v go!"." = a :: b :: r ∧ asciiStr a ∧ asciiStr b ∧ r ≠ [] := by
  obtain ⟨a, b, r, rfl, ha, hb⟩ := h
  refine ⟨a, b, strings.splitAux go!"." r [], ?_, version.decDigits_ascii ha,
    version.decDigits_ascii hb, version.splitAux_ne_nil _ _ _⟩
  have e : a ++ go!"." ++ b ++ go!"." ++ r = a ++ W8 46 :: (b ++ W8 46 :: r) := by simp
  unfold strings.split
  rw [e, version.splitAux_dot _ _ _ (version.decDigits_noDot ha),
    version.splitAux_dot _ _ _ (version.decDigits_noDot hb)]
  simp

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.version.Assumptions]

theorem version.Cluster.wp_proof
    (wp_NewVersion : semver.NewVersion.spec (GF := GF) (hG := hG))
    (wp_Major : semver.Version.Major.spec (GF := GF) (hG := hG))
    (wp_Minor : semver.Version.Minor.spec (GF := GF) (hG := hG))
    (wp_Sprintf : _root_.Perennial.fmt.Sprintf.spec (GF := GF) (hG := hG))
    (wp_Split : strings.Split.spec (GF := GF) (hG := hG)) :
    version.Cluster.spec (GF := GF) (hG := hG) := by
  intro v
  wp_start as #Hpkg
  ihave #Hsv : isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 $$ []
  · iPkgInit
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  ihave #Hstr : isPkgInit (PROP := IProp GF) pkg_id.strings $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_NewVersion v as %pv %err Hr
  icases Hr with (⟨%Hok, %x, #Hx, #His⟩ | %Hbad)
  · obtain ⟨-, -, Herr⟩ := Hok
    subst Herr
    wp_auto
    wp_apply wp_Major $$ [$Hx] as -
    wp_apply wp_Minor $$ [$Hx] as -
    wp_apply (wp_slice_literal (l := [_, _]))
    try (isplitr; (ipureintro; rfl))
    iintro %sla ⟨Hargs, -⟩
    wp_auto
    wp_apply (fmt.wp_Sprintf_pure wp_Sprintf go!"%d.%d" [.dir none _root_.Perennial.fmt.verb_d, .lit go!".", .dir none _root_.Perennial.fmt.verb_d] _ _ _ _
      (by fmt_encode) (by fmt_fits) (.int _ _ _ _ (.uint64 _) (.int _ _ _ _ (.uint64 _) .nil)))
      $$ [$Hargs] as %str ⟨-, %Hout⟩
    iapply HΦ
    ipureintro
    intro _
    rw [Hout]
    simp (config := { decide := true }) only [_root_.Perennial.fmt.dirOutFn, _root_.Perennial.fmt.render, Option.getD_none, List.append_nil, ↓reduceIte]
    exact version.ascii_append (version.decimalPad0_ascii _)
      (version.ascii_append (by intro c hc; simp only [List.mem_singleton] at hc; subst hc; decide)
        (version.decimalPad0_ascii _))
  · obtain ⟨-, Herr⟩ := Hbad
    cases err with
    | nil => exact absurd rfl Herr
    | ok i =>
    simp only
    wp_auto
    wp_apply wp_Split v go!"." (by decide) as %vsl ⟨Hvs, -⟩
    ihave %Hlen := ownSlice_len $$ Hvs
    obtain ⟨l, hsp⟩ : ∃ l, strings.split v go!"." = l := ⟨_, rfl⟩
    rw [hsp] at Hlen ⊢
    wp_if_destruct
    · iapply HΦ
      ipureintro
      intro hv
      exfalso
      obtain ⟨a, b, r, hs, -, -, hr⟩ := version.split_semverStr hv
      rw [hs] at hsp
      subst hsp
      obtain ⟨h1, -⟩ := Hlen
      simp only [List.length_cons] at h1
      have := List.length_pos_iff.mpr hr
      word
    rcases l with _ | ⟨a, _ | ⟨b, r⟩⟩
    · obtain ⟨h1, -⟩ := Hlen
      simp only [List.length_nil] at h1
      word
    · obtain ⟨h1, -⟩ := Hlen
      simp only [List.length_cons, List.length_nil] at h1
      word
    obtain ⟨h1, -⟩ := Hlen
    simp only [List.length_cons] at h1
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z vsl.len by word)]
    wp_apply wp_load_slice_index vsl (sint.Z (W64 0)) _ _ a (by word) $$ [Hvs] as Hvs
    · iframe; ipureintro; rfl
    try wp_auto
    rw [ite_eq_left (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) < sint.Z vsl.len by word)]
    wp_apply wp_load_slice_index vsl (sint.Z (W64 1)) _ _ b (by word) $$ [Hvs] as Hvs
    · iframe; ipureintro; rfl
    try wp_auto
    wp_apply (wp_slice_literal (l := [_, _]))
    try (isplitr; (ipureintro; rfl))
    iintro %sla ⟨Hargs, -⟩
    wp_auto
    wp_apply (fmt.wp_Sprintf_pure wp_Sprintf go!"%s.%s" [.dir none _root_.Perennial.fmt.verb_s, .lit go!".", .dir none _root_.Perennial.fmt.verb_s] _ _ _ _
      (by fmt_encode) (by fmt_fits) (.str _ _ _ (.str _ _ _ .nil)))
      $$ [$Hargs] as %str ⟨-, %Hout⟩
    iapply HΦ
    ipureintro
    intro hv
    rw [Hout]
    simp (config := { decide := true }) only [_root_.Perennial.fmt.dirOutFn, _root_.Perennial.fmt.render, List.append_nil, ↓reduceIte]
    obtain ⟨a', b', r', hs, ha, hb, -⟩ := version.split_semverStr hv
    rw [hs] at hsp
    simp only [List.cons.injEq] at hsp
    obtain ⟨rfl, rfl, -⟩ := hsp
    exact version.ascii_append ha
      (version.ascii_append (by intro c hc; simp only [List.mem_singleton] at hc; subst hc; decide) hb)

end proof

end EtcdGrove
end Perennial
