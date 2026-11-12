/-
`tx.write()`'s loops (U10c, `notes/bbolt-proof-plan.md`): the lemmas its proof uses inside the
first loop (the dirty pages per key, `wrKey`; at most `lim` keys below `lim`), on a failed write
(the interrupted page's slots, `cur_any`; the written pages' slots, `sd_any`), after the writes
(the written pages as their buffers and their slots, `pgBuf`, `done_split`) and in the zeroing
loop (`zero_step`).
-/
module

public import Proof.go_etcd_io.bbolt.Commit.WritePage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- A key of the dirty pages, before `tx.write`'s first loop: its buffer, and its slots. -/
def wrKey (b : Loc) (p : GoString) (pm : GMap w64 Loc) (bufs : GMap w64 (List w8)) (k : w64) :
    IProp GF :=
  iprop((∃ pl, ⌜pm !! k = some pl⌝ ∗ ∃ bs, ⌜bufs !! k = some bs⌝ ∗
      bytesPointsto pl (DFrac.own 1) bs) ∗
    (∃ pg, ⌜bufs !! k = some pg⌝ ∗
      [∗list] s ∈ List.range' k.toNat (1 + pageOverflow pg), slotAny b p s))

omit [GooseExts] in
theorem wr_drop_cons {α : Type} (l : List α) (n : Nat) (x : α) (h : l[n]? = some x) :
    l.drop n = x :: l.drop (n + 1) := by
  have hn : n < l.length := (List.getElem?_eq_some_iff.mp h).1
  rw [List.drop_eq_getElem_cons hn]
  rw [List.getElem?_eq_getElem hn] at h
  rw [Option.some.inj h]

/-- At most `lim` distinct keys below `lim`. -/
theorem wr_keys_le (keys : List w64) (lim : Nat) (hnd : keys.Nodup)
    (h : ∀ k ∈ keys, k.toNat < lim) : keys.length ≤ lim := by
  have hnd' : (keys.map BitVec.toNat).Nodup :=
    List.Pairwise.map _ (fun a b hab h => hab (BitVec.eq_of_toNat_eq h)) hnd
  have hsub : keys.map BitVec.toNat ⊆ List.range lim := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact List.mem_range.2 (h k hk)
  have := (List.subperm_of_subset hnd' hsub).length_le
  simpa using this

/-- A page interrupted by a failed write: its slots, holding anything. -/
theorem cur_any (b : Loc) (p : GoString) (k c' w cs r : Nat) (ysd ys : List (w8 × Bool))
    (P : List w8) (hysd : ysd.length = w) (hP : P.length = w) (hys : ys.length = cs)
    (htot : w + cs + r = 4096 * c') :
    osBytes (GF := GF) p (4096 * k) (DFrac.own 1) ysd ∗
      bytesPointsto (b +ₗ ((4096 * k : Nat) : Int)) (DFrac.own (1 : Qp).half) P ∗
      osBytes p (4096 * k + w) (DFrac.own 1) ys ∗ cAny b (4096 * k + w) cs ∗
      oAny p (4096 * k + w + cs) r ∗ cAny b (4096 * k + w + cs) r ⊢
      [∗list] s ∈ List.range' k c', slotAny b p s := by
  iintro ⟨H1, H2, H3, H4, H5, H6⟩
  iapply (slotsAny_run b p c' k).2
  rw [← htot, Nat.add_assoc w cs r]
  isplitl [H1 H3 H5]
  · iapply (oAny_app p _ w _).2
    isplitl [H1]
    · unfold oAny; iexists ysd; iframe H1; ipureintro; exact hysd
    iapply (oAny_app p _ cs _).2
    isplitl [H3]
    · unfold oAny; iexists ys; iframe H3; ipureintro; exact hys
    iexact H5
  · iapply (cAny_app b _ w _).2
    isplitl [H2]
    · ihave H2 := bytes_cellsR b P (4096 * k) $$ H2
      rw [hP]
      unfold cAny; iexists _; iexact H2
    iapply (cAny_app b _ cs _).2
    iframe

/-- A written page's buffer: its header, and the rest. -/
def pgBuf (e : w64 × Loc × List w8) : IProp GF :=
  iprop(e.2.1 ↦ pageHdr e.2.2 ∗ ⌜0 < e.2.1.addr⌝ ∗
    bytesPointsto (e.2.1 +ₗ 16) (DFrac.own 1) (e.2.2.drop 16))

/-- The written pages, as their buffers and their slots. -/
theorem done_split (b : Loc) (p : GoString) (L : List (w64 × Loc × List w8)) :
    ([∗list] e ∈ L, e.2.1 ↦ pageHdr e.2.2) ∗ ([∗list] e ∈ L, pgDone (GF := GF) b p e) ⊢
      ([∗list] e ∈ L, pgBuf e) ∗
      [∗list] e ∈ L, [∗list] s ∈ List.range' e.1.toNat (1 + pageOverflow e.2.2),
        slotDone b p s (pageChunk e.2.2 (s - e.1.toNat)) := by
  iintro ⟨Hh, Hd⟩
  ihave H := (BigSepL.bigSepL_sep_eqv (Φ := fun _ e => iprop(e.2.1 ↦ pageHdr e.2.2))
    (Ψ := fun _ e => pgDone (GF := GF) b p e)).2 $$ [Hh Hd]
  · iframe
  iapply BigSepL.bigSepL_sep_eqv.1
  iapply BigSepL.bigSepL_mono ?_ $$ H
  intro i e _
  unfold pgDone pgBuf
  iintro ⟨Hh, %Hp, Hr, Hs⟩
  iframe
  ipureintro; exact Hp

/-- The written pages' slots, holding anything. -/
theorem sd_any (b : Loc) (p : GoString) (L : List (w64 × Loc × List w8))
    (hl : ∀ e ∈ L, e.2.2.length = 4096 * (1 + pageOverflow e.2.2)) :
    ([∗list] e ∈ L, [∗list] s ∈ List.range' e.1.toNat (1 + pageOverflow e.2.2),
        slotDone (GF := GF) b p s (pageChunk e.2.2 (s - e.1.toNat))) ⊢
      [∗list] e ∈ L, [∗list] s ∈ List.range' e.1.toNat (1 + pageOverflow e.2.2),
        slotAny b p s := by
  apply BigSepL.bigSepL_mono
  intro i e he
  apply BigSepL.bigSepL_mono
  intro k s hs
  have hm := List.mem_range'_1.1 (List.mem_of_getElem? hs)
  exact slotDone_any b p s _
    (pageChunk_length _ _ _ (hl e (List.mem_of_getElem? he)) (by omega))

omit [GooseExts] in
theorem zero_step (bs : List w8) (k : Nat) (hk : k < bs.length) :
    (List.replicate k (W8 0) ++ bs.drop k).set k (W8 0) =
      List.replicate (k + 1) (W8 0) ++ bs.drop (k + 1) := by
  apply List.ext_getElem?; intro i
  rw [List.getElem?_set]
  have hl : (List.replicate k (W8 0) ++ bs.drop k).length = bs.length := by simp; omega
  by_cases hik : k = i
  · subst hik
    rw [if_pos rfl, if_pos (by rw [hl]; exact hk), List.getElem?_append_left (by simp)]
    simp
  · rw [if_neg hik]
    by_cases hi : i < k
    · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simp; omega)]
      simp [hi, show i < k + 1 by omega]
    · rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
      simp only [List.length_replicate, List.getElem?_drop]
      congr 1; omega

end proof

end bbolt
end EtcdGrove
end Perennial
