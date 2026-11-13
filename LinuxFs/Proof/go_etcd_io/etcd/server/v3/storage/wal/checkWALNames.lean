/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/checkWALNames.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.checkWALNames
public import Spec.strings.HasSuffix
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Logger__Warn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-- The selection of a prefix extended by one name. -/
theorem walNamesSel_snoc {names ws : List GoString} {n : GoString} (h : WalNamesSel names ws)
    (hp : walNameMay n) : WalNamesSel (names ++ [n]) (ws ++ [n]) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.append (List.Sublist.refl _), ?_, ?_⟩
  · intro b hb
    rcases List.mem_append.1 hb with hb | hb
    · exact h2 b hb
    · rw [List.mem_singleton.1 hb]; exact hp
  · intro b hb hbp
    rcases List.mem_append.1 hb with hb | hb
    · exact List.mem_append_left _ (h3 b hb hbp)
    · rw [List.mem_singleton.1 hb]; exact List.mem_append_right _ (List.mem_singleton_self _)

/-- … or skipping it. -/
theorem walNamesSel_skip {names ws : List GoString} {n : GoString} (h : WalNamesSel names ws)
    (hp : ¬ walNameParses n) : WalNamesSel (names ++ [n]) ws := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1.trans (List.sublist_append_left _ _), h2, ?_⟩
  intro b hb hbp
  rcases List.mem_append.1 hb with hb | hb
  · exact h3 b hb hbp
  · rw [List.mem_singleton.1 hb] at hbp; exact absurd hbp hp

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.checkWALNames.wp_proof
    (HParse : go_etcd_io.etcd.server.v3.storage.wal.parseWALName.spec (GF := GF) (hG := hG))
    (HSuf : strings.HasSuffix.spec (GF := GF) (hG := hG))
    (HStr : zap.String.spec (GF := GF) (hG := hG))
    (HWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.checkWALNames.spec (GF := GF) (hG := hG) := by
  intro lg sl names dq
  wp_start as ⟨#Hlg, Hsl⟩
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  wp_apply (wp_slice_make2 (V := GoString) (W64 0)) as %w0 ⟨Hw0, Hc0⟩
  · ipureintro; decide
  (try wp_auto)
  ihave IH : iprop(∃ (j : w64) (nv : GoString) (wsl : GoSlice) (ws : List GoString),
      "i" ∷ i_ptr ↦ j ∗ "name" ∷ name_ptr ↦ nv ∗ "wnames" ∷ wnames_ptr ↦ wsl ∗
      "Hw" ∷ wsl ↦* ws ∗ "Hwc" ∷ ownSliceCap GoString wsl (DFrac.own 1) ∗
      "Hsl" ∷ sl ↦*{dq} names ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ names.length ∧
        WalNamesSel (names.take (sint.nat j)) ws⌝) $$ [i name wnames Hw0 Hc0 Hsl]
  · iexists W64 0, _, w0, []
    simp only [named]
    iframe
    ipureintro
    refine ⟨by decide, by simp, ?_⟩
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
    exact ⟨List.Sublist.slnil, by simp, by simp⟩
  wp_for IH
  obtain ⟨Hj0, Hjl, Hjs⟩ := Hj
  wp_if_destruct
  · have hjl : sint.nat j < names.length := by
      have : sint.Z j < sint.Z sl.len := Hif
      word
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hj0, by word⟩)]
    obtain ⟨n, hn⟩ : ∃ n, names[sint.nat j]? = some n := ⟨_, List.getElem?_eq_getElem hjl⟩
    have htake : names.take (sint.nat (j + W64 1)) = names.take (sint.nat j) ++ [n] := by
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, List.take_succ, hn]; rfl
    wp_apply wp_load_slice_index sl (sint.Z j) names dq n Hj0 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact hn
    try wp_auto
    wp_apply HParse n $$ [] as %seq %idx %err %Hp
    try wp_auto
    cases err with
    | ok ie =>
      -- an error: skipped (maybe logged)
      have hnp : ¬ walNameParses n := fun ⟨hs, x, y, hsc⟩ => by
        have := (Hp.1 x y hs hsc).1; cases this
      wp_auto
      wp_apply HSuf n (go!".tmp")
      wp_if_destruct
      · try wp_auto
        wp_for_post
        iframe
        iexists j + W64 1, n, wsl, ws
        simp only [named]
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [htake]; exact walNamesSel_skip Hjs hnp
      · wp_apply HStr as %f -
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %fsl ⟨-, -⟩
        try wp_auto
        wp_apply HWarn lg _ _ $$ []
        · iapply zapLoggerOk_ne_null; iexact Hlg
        try wp_auto
        wp_for_post
        iframe
        iexists j + W64 1, n, wsl, ws
        simp only [named]
        iframe
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [htake]; exact walNamesSel_skip Hjs hnp
    | nil =>
      have hmay : walNameMay n := by
        refine ⟨?_, ?_⟩
        · apply Classical.byContradiction; intro hs; exact (Hp.2 (Or.inl hs)) rfl
        · intro he; exact (Hp.2 (Or.inr he)) rfl
      wp_auto
      wp_apply wp_slice_literal [n]
      isplitr
      · ipureintro; rfl
      iintro %sl1 ⟨Hsl1, -⟩
      wp_apply wp_slice_append $$ [$Hw $Hwc $Hsl1] as %sl' ⟨Hw, Hwc, -⟩
      try wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, n, sl', ws ++ [n]
      simp only [named]
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [htake]; exact walNamesSel_snoc Hjs hmay
  · have hj : sint.nat j = names.length := by
      have : ¬ sint.Z j < sint.Z sl.len := Hif
      word
    rw [hj, List.take_length] at Hjs
    try wp_auto
    iapply HΦ
    iframe
    ipureintro; exact Hjs

end proof

end EtcdGrove
end Perennial
