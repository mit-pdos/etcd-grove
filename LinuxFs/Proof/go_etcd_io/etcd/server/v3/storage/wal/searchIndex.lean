/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/searchIndex.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.searchIndex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-- A segment's name ends in `.wal`. -/
theorem walNameStr_suffix (s i : w64) : go!".wal" <:+ fmt.walNameStr s i :=
  ⟨fmt.hexPad 16 (uint.nat s) ++ W8 45 :: fmt.hexPad 16 (uint.nat i), by simp [fmt.walNameStr]⟩

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.searchIndex.wp_proof
    (HParse : go_etcd_io.etcd.server.v3.storage.wal.parseWALName.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.searchIndex.spec (GF := GF) (hG := hG) := by
  intro lg sl names dq index hnames
  wp_start as Hsl
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  have hl : (names.length : Int) = sint.Z sl.len := by rw [Hlen.1]; word
  have hl63 : (names.length : Int) < 2 ^ 63 := by have := hl; word
  ihave IH : iprop(∃ (k : Int), "i" ∷ i_ptr ↦ W64 k ∗ "Hsl" ∷ sl ↦*{dq} names ∗
      "%Hk" ∷ ⌜-1 ≤ k ∧ k < names.length ∧
        walSearch (names.map walNameIdx) index =
          walSearchFrom (names.map walNameIdx) index (k + 1).toNat⌝) $$ [i Hsl]
  · iexists (names.length : Int) - 1
    simp only [named]
    rw [show W64 ((names.length : Int) - 1) = sl.len - W64 1 by word]
    iframe
    ipureintro
    refine ⟨by omega, by omega, ?_⟩
    rw [show ((names.length : Int) - 1 + 1).toNat = (names.map walNameIdx).length by simp]
    rfl
  wp_for IH
  obtain ⟨Hk1, Hkl, Hks⟩ := Hk
  have hkz : sint.Z (W64 k) = k := by word
  wp_if_destruct
  · have hk0 : 0 ≤ k := by
      have := Hif; rw [hkz] at this; simpa using this
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
    obtain ⟨n, hn⟩ : ∃ n, names[k.toNat]? = some n :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    wp_apply wp_load_slice_index sl (sint.Z (W64 k)) names dq n (by omega) $$ [Hsl] as Hsl
    · iframe; ipureintro; rw [hkz]; exact hn
    try wp_auto
    obtain ⟨sq, ix, rfl⟩ := hnames n (List.mem_of_getElem? hn)
    wp_apply HParse (fmt.walNameStr sq ix) as %seq %idx %err %Hp
    obtain ⟨rfl, rfl, rfl⟩ := Hp.1 sq ix (walNameStr_suffix sq ix) (fmt.scanWalName_walNameStr sq ix)
    try wp_auto
    have hidx : (names.map walNameIdx).getD k.toNat 0 = idx := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, hn]
      simp [walNameIdx, fmt.scanWalName_walNameStr]
    have hstep : walSearchFrom (names.map walNameIdx) index (k + 1).toNat =
        if uint.Z idx ≤ uint.Z index then some k.toNat
        else walSearchFrom (names.map walNameIdx) index k.toNat := by
      rw [show (k + 1).toNat = k.toNat + 1 by omega, walSearchFrom, hidx]
    wp_if_destruct
    · wp_for_post
      rw [Hks, hstep, ite_eq_left Hif]
      simp only [Option.isSome_some]
      rw [show W64 ((k.toNat : Nat) : Int) = W64 k by congr 1; omega]
      iapply HΦ
      iframe
    · wp_for_post
      iframe
      iexists k - 1
      simp only [named]
      rw [show W64 k - W64 1 = W64 (k - 1) by word]
      iframe
      ipureintro
      refine ⟨by omega, by omega, ?_⟩
      rw [Hks, hstep, ite_eq_right Hif, show (k - 1 + 1).toNat = k.toNat by omega]
  · have hk : k = -1 := by
      have : ¬ sint.Z (W64 0) ≤ sint.Z (W64 k) := Hif
      rw [hkz] at this
      simp at this; omega
    subst hk
    rw [show ((-1 : Int) + 1).toNat = 0 by rfl, walSearchFrom] at Hks
    rw [Hks]
    simp only [Option.isSome_none]
    iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial
