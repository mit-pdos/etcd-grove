/-
Proof of `Spec/google_golang_org/grpc/internal/mem/newBinaryTiered.lean` (grpc-mem, 2026-11-26): the
exponents sorted (`slices.Sort` at `uint8`) and compacted (the model's `compactExponents`) stay at most
`62`, so the loop never takes its `fmt.Errorf` branch and indexes the two 63-entry tables
(`slices.Repeat([]int{-1}, 63)`) in range; the two gap-filling loops index them in range too.
-/
module

public import Spec.google_golang_org.grpc.internal.mem.newBinaryTiered
public import Spec.google_golang_org.grpc.internal.mem.compactExponents
public import Perennial.Spec.slices.Repeat
public import Perennial.Proof.slices.Results

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The builtin `max` of two `int`s: one of them, at least both. -/
theorem grpc.internal.mem.wp_max_int (x y : w64) :
    {{ (True : IProp GF) }}
      (App (App (Val #(functions go.max [go.int, go.int])) (Val #x)) (Val #y))
    {{ (m : w64), RET #m; ⌜(m = x ∨ m = y) ∧ sint.Z x ≤ sint.Z m ∧ sint.Z y ≤ sint.Z m⌝ }} := by
  wp_start
  wp_if_destruct
  · iapply HΦ; ipureintro; refine ⟨Or.inl rfl, Int.le_refl _, ?_⟩; word
  · iapply HΦ; ipureintro; refine ⟨Or.inr rfl, ?_, Int.le_refl _⟩; word

end proof

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : google_golang_org.grpc.internal.mem.Assumptions]

theorem grpc.internal.mem.newBinaryTiered.wp_proof
    (wp_compactExponents : grpc.internal.mem.compactExponents.spec (GF := GF) (hG := hG))
    (wp_Repeat : _root_.Perennial.slices.Repeat.spec (GF := GF) (hG := hG)) :
    grpc.internal.mem.newBinaryTiered.spec (GF := GF) (hG := hG) := by
  intro f fb s xs Hxs Hlen
  wp_start as ⟨Hs, #Hf⟩
  ihave #Hfact : (_root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.mem.internalMemInit
      (hG := hG) : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  unfold _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.mem.internalMemInit
  wp_auto
  wp_apply _root_.Perennial.slices.wp_Sort_uint8 s xs $$ [Hs] as %xs1 ⟨Hs, %Hperm, %-⟩
  · iframe Hs; iframe #; ipureintro; exact Hlen
  try wp_auto
  wp_apply wp_compactExponents s xs1 $$ [Hs] as %s2 %ys ⟨Hs2, %Hys⟩
  · iexact Hs
  have Hys62 : ∀ y ∈ ys, uint.Z y ≤ 62 := fun y hy => Hxs y (Hperm.mem_iff.2 (Hys y hy))
  try wp_auto
  rw [show W64 64 - W64 2 = W64 62 from rfl]
  wp_apply (wp_slice_literal (V := w64) (l := _)); isplitr; (· ipureintro; rfl); iintro %l1 ⟨L1, -⟩
  try wp_auto
  wp_apply wp_Repeat (V := w64) _ (DFrac.own 1) [W64 (-1)] (W64 62 + W64 1) (by word) (by simp; word)
    $$ [L1] as %a1 ⟨-, Ha1, -⟩
  · iexact L1
  try wp_auto
  wp_apply (wp_slice_literal (V := w64) (l := _)); isplitr; (· ipureintro; rfl); iintro %l2 ⟨L2, -⟩
  try wp_auto
  wp_apply wp_Repeat (V := w64) _ (DFrac.own 1) [W64 (-1)] (W64 62 + W64 1) (by word) (by simp; word)
    $$ [L2] as %a2 ⟨-, Ha2, -⟩
  · iexact L2
  try wp_auto
  have h63 : ((List.replicate (sint.nat (W64 62 + W64 1)) [W64 (-1)]).flatten).length = 63 := by
    simp; rfl
  generalize (List.replicate (sint.nat (W64 62 + W64 1)) [W64 (-1)]).flatten = t0 at h63 ⊢
  ihave %Hys := ownSlice_len _ _ _ $$ Hs2
  wp_apply wp_slice_make3 (V := GoInterface) (W64 0) s2.len ⟨by word, by word⟩ as %pl ⟨Hpl, Hplc, -⟩
  try wp_auto
  irename i => rI
  irename i => ui
  rename_i ui_ptr
  -- the loop over the exponents: the tables keep 63 entries, the pools grow
  ihave IH : iprop(∃ (n : w64) (t1 t2 : List w64) (pl' : GoSlice) (ps : List GoInterface) (e : w8)
      (ii mt : w64),
      "rI" ∷ i_ptr ↦ n ∗ "Hs2" ∷ s2 ↦* ys ∗
      "Ha1" ∷ a1 ↦* t1 ∗ "Ha2" ∷ a2 ↦* t2 ∗
      "pools" ∷ pools_ptr ↦ pl' ∗ "Hpl" ∷ pl' ↦* ps ∗ "Hplc" ∷ ownSliceCap GoInterface pl' (DFrac.own 1) ∗
      "exp" ∷ exp_ptr ↦ e ∗ "ui" ∷ ui_ptr ↦ ii ∗ "maxTier" ∷ maxTier_ptr ↦ mt ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z s2.len ∧ t1.length = 63 ∧ t2.length = 63⌝)
    $$ [rI Hs2 Ha1 Ha2 pools Hpl Hplc exp ui maxTier]
  · iexists (W64 0), t0, t0, pl, _, _, _, _
    iframe
    ipureintro; exact ⟨by word, by word, h63, h63⟩
  wp_for IH
  wp_if_destruct
  · obtain ⟨Hn0, Hnl, Ht1, Ht2⟩ := Hn
    have Hif' : sint.Z n < sint.Z s2.len := by simpa using Hif
    obtain ⟨e0, He0⟩ : ∃ y, ys[(sint.Z n).toNat]? = some y :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    have He62 : uint.Z e0 ≤ 62 := Hys62 e0 (List.mem_of_getElem? He0)
    rw [ite_eq_left ⟨Hn0, Hif'⟩]
    wp_apply wp_load_slice_index s2 (sint.Z n) ys (DFrac.own 1) e0 Hn0 $$ [Hs2] as Hs2
    · iframe Hs2; ipureintro; exact He0
    try wp_auto
    wp_if_destruct
    · exfalso; word
    try wp_auto
    wp_apply Hf as %pv -
    try wp_auto
    wp_apply (wp_slice_literal (V := GoInterface) (l := [pv])); isplitr; (· ipureintro; rfl)
    iintro %lp ⟨Lp, -⟩
    try wp_auto
    wp_apply wp_slice_append pl' ps _ [pv] (DFrac.own 1) $$ [Hpl Hplc Lp] as %pl2 ⟨Hpl, Hplc, -⟩
    · iframe Hpl Hplc Lp
    try wp_auto
    ihave %Ha1l := ownSlice_len _ _ _ $$ Ha1
    ihave %Ha2l := ownSlice_len _ _ _ $$ Ha2
    have hix : 0 ≤ sint.Z (W64 (uint.Z e0)) ∧ sint.Z (W64 (uint.Z e0)) < sint.Z a1.len := ⟨by word, by word⟩
    have hix2 : 0 ≤ sint.Z (W64 (uint.Z e0)) ∧ sint.Z (W64 (uint.Z e0)) < sint.Z a2.len := ⟨by word, by word⟩
    wp_apply grpc.internal.mem.wp_max_int as %m -
    try wp_auto
    rw [ite_eq_left hix]
    wp_apply wp_store_slice_index a1 (sint.Z (W64 (uint.Z e0))) t1 n $$ [Ha1] as Ha1
    · iframe Ha1; ipureintro; exact ⟨hix.1, by word⟩
    try wp_auto
    rw [ite_eq_left hix2]
    wp_apply wp_store_slice_index a2 (sint.Z (W64 (uint.Z e0))) t2 n $$ [Ha2] as Ha2
    · iframe Ha2; ipureintro; exact ⟨hix2.1, by word⟩
    try wp_auto
    wp_for_post
    iframe
    iexists (n + W64 1), _, _, pl2, _, e0, n, m
    iframe
    ipureintro
    refine ⟨by word, by word, by rw [List.length_set]; exact Ht1, by rw [List.length_set]; exact Ht2⟩
  · -- after the loop: fill the gaps of the tables
    obtain ⟨Hn0, Hnl, Ht1, Ht2⟩ := Hn
    ihave IHa : iprop(∃ (j : w64) (u1 : List w64), "i" ∷ i_ptr ↦ j ∗ "Ha1" ∷ a1 ↦* u1 ∗
        "%Hj" ∷ ⌜u1.length = 63 ∧ -1 ≤ sint.Z j ∧ sint.Z j ≤ 61⌝) $$ [i Ha1]
    · iexists _, t1; iframe; ipureintro; exact ⟨Ht1, by word, by word⟩
    wp_for IHa
    wp_if_destruct
    · obtain ⟨Hu1, Hj0, Hj61⟩ := Hj
      have Hif' : sint.Z j ≥ sint.Z (W64 0) := by simpa using Hif
      ihave %Ha1l := ownSlice_len _ _ _ $$ Ha1
      have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z a1.len := ⟨by word, by word⟩
      have hb1 : 0 ≤ sint.Z (j + W64 1) ∧ sint.Z (j + W64 1) < sint.Z a1.len := ⟨by word, by word⟩
      obtain ⟨y, Hy⟩ : ∃ y, u1[(sint.Z j).toNat]? = some y := ⟨_, List.getElem?_eq_getElem (by word)⟩
      obtain ⟨y1, Hy1⟩ : ∃ y, u1[(sint.Z (j + W64 1)).toNat]? = some y :=
        ⟨_, List.getElem?_eq_getElem (by word)⟩
      try wp_auto
      rw [ite_eq_left hb]
      wp_apply wp_load_slice_index a1 (sint.Z j) u1 (DFrac.own 1) y hb.1 $$ [Ha1] as Ha1
      · iframe Ha1; ipureintro; exact Hy
      try wp_auto
      wp_if_destruct
      · try wp_auto
        rw [ite_eq_left hb1]
        wp_apply wp_load_slice_index a1 (sint.Z (j + W64 1)) u1 (DFrac.own 1) y1 hb1.1 $$ [Ha1] as Ha1
        · iframe Ha1; ipureintro; exact Hy1
        try wp_auto
        rw [ite_eq_left hb]
        wp_apply wp_store_slice_index a1 (sint.Z j) u1 y1 $$ [Ha1] as Ha1
        · iframe Ha1; ipureintro; exact ⟨hb.1, by word⟩
        try wp_auto
        wp_for_post
        iframe
        iexists (j - W64 1), _
        iframe
        ipureintro; exact ⟨by rw [List.length_set]; exact Hu1, by word, by word⟩
      · wp_for_post
        iframe
        iexists (j - W64 1), u1
        iframe
        ipureintro; exact ⟨Hu1, by word, by word⟩
    · ihave IHb : iprop(∃ (j : w64) (u2 : List w64), "i" ∷ i_ptr ↦ j ∗ "Ha2" ∷ a2 ↦* u2 ∗
          "%Hj" ∷ ⌜u2.length = 63 ∧ 1 ≤ sint.Z j ∧ sint.Z j ≤ 63⌝) $$ [i Ha2]
      · iexists _, t2; iframe; ipureintro; exact ⟨Ht2, by word, by word⟩
      wp_for IHb
      wp_if_destruct
      · obtain ⟨Hu2, Hj1, Hj63⟩ := Hj
        have Hif' : sint.Z j ≤ sint.Z (W64 62) := by simpa using Hif
        ihave %Ha2l := ownSlice_len _ _ _ $$ Ha2
        have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z a2.len := ⟨by word, by word⟩
        have hb1 : 0 ≤ sint.Z (j - W64 1) ∧ sint.Z (j - W64 1) < sint.Z a2.len := ⟨by word, by word⟩
        obtain ⟨y, Hy⟩ : ∃ y, u2[(sint.Z j).toNat]? = some y := ⟨_, List.getElem?_eq_getElem (by word)⟩
        obtain ⟨y1, Hy1⟩ : ∃ y, u2[(sint.Z (j - W64 1)).toNat]? = some y :=
          ⟨_, List.getElem?_eq_getElem (by word)⟩
        try wp_auto
        rw [ite_eq_left hb]
        wp_apply wp_load_slice_index a2 (sint.Z j) u2 (DFrac.own 1) y hb.1 $$ [Ha2] as Ha2
        · iframe Ha2; ipureintro; exact Hy
        try wp_auto
        wp_if_destruct
        · try wp_auto
          rw [ite_eq_left hb1]
          wp_apply wp_load_slice_index a2 (sint.Z (j - W64 1)) u2 (DFrac.own 1) y1 hb1.1 $$ [Ha2] as Ha2
          · iframe Ha2; ipureintro; exact Hy1
          try wp_auto
          rw [ite_eq_left hb]
          wp_apply wp_store_slice_index a2 (sint.Z j) u2 y1 $$ [Ha2] as Ha2
          · iframe Ha2; ipureintro; exact ⟨hb.1, by word⟩
          try wp_auto
          wp_for_post
          iframe
          iexists (j + W64 1), _
          iframe
          ipureintro; exact ⟨by rw [List.length_set]; exact Hu2, by word, by word⟩
        · wp_for_post
          iframe
          iexists (j + W64 1), u2
          iframe
          ipureintro; exact ⟨Hu2, by word, by word⟩
      · -- `return &BinaryTieredBufferPool{...}, nil`
        try wp_auto
        wp_end

end proof

end EtcdGrove
end Perennial
