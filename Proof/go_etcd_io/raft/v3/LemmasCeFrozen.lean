/-
Pure lemmas on a `Ready`'s committed entries `ce` (U8 v2 step 4): the part of them a hand-out
freezes (`frozenRdy`) and their terms in raft's log.
-/
module

public import Proof.go_etcd_io.raft.v3.InvReadylog

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section lemmas
variable [GooseExts]

/-- The committed entries `ce` (after `applying`) are raft's log entries there. -/
theorem ce_log_at (ls : LogState) (d ce : List EntryM)
    (Hdl : d.length = uint.nat ls.applying)
    (Hpa : uint.nat ls.prev.index' ≤ uint.nat ls.applying)
    (Hcm : uint.Z ls.committed ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
      + (ls.uents.length : Int))
    (Hcel : uint.nat ls.applying + ce.length ≤ uint.nat ls.committed)
    (Hag : ∀ k e, (ls.sents ++ ls.uents)[k]? = some e →
      uint.nat ls.prev.index' + k < (d ++ ce).length →
      (d ++ ce)[uint.nat ls.prev.index' + k]? = some e)
    (k : Nat) (e : EntryM) (Hk : ce[k]? = some e) :
    (ls.sents ++ ls.uents)[uint.nat ls.applying - uint.nat ls.prev.index' + k]? = some e := by
  have Hkl := (List.getElem?_eq_some_iff.mp Hk).1
  have Hlen : uint.nat ls.applying - uint.nat ls.prev.index' + k < (ls.sents ++ ls.uents).length := by
    rw [List.length_append]; word
  obtain ⟨e', He'⟩ : ∃ e', (ls.sents ++ ls.uents)[uint.nat ls.applying - uint.nat ls.prev.index' + k]?
      = some e' := ⟨_, List.getElem?_eq_getElem Hlen⟩
  have H := Hag _ e' He' (by rw [List.length_append]; omega)
  rw [show uint.nat ls.prev.index' + (uint.nat ls.applying - uint.nat ls.prev.index' + k)
    = d.length + k by omega, List.getElem?_append_right (by omega),
    show d.length + k - d.length = k by omega, Hk] at H
  rw [He', H]

/-- What a `Ready`'s hand-out freezes of its committed entries `ce`: their first
`min |ce| (frozenEnd - applying)`; and when that is not all of them, the batch it hands out
(`nextUnstable`) starts right after the frozen ones. -/
theorem ceFrozen_pure (ls : LogState) (d ce : List EntryM)
    (Hdl : d.length = uint.nat ls.applying)
    (Hpa : uint.nat ls.prev.index' ≤ uint.nat ls.applying)
    (Hidx : LogIndicesOk ls.prev (ls.sents ++ ls.uents))
    (Hcm : uint.Z ls.committed ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
      + (ls.uents.length : Int))
    (Hip : logOffset ls ≤ uint.Z ls.inprogress ∧
      uint.Z ls.inprogress ≤ logOffset ls + (ls.uents.length : Int))
    (Hai : uint.nat ls.applying < uint.nat ls.inprogress)
    (Hcel : uint.nat ls.applying + ce.length ≤ uint.nat ls.committed)
    (Hag : ∀ k e, (ls.sents ++ ls.uents)[k]? = some e →
      uint.nat ls.prev.index' + k < (d ++ ce).length →
      (d ++ ce)[uint.nat ls.prev.index' + k]? = some e) :
    (frozenRdy ls).take (min ce.length (frozenEnd ls - uint.nat ls.applying)) =
        ce.take (min ce.length (frozenEnd ls - uint.nat ls.applying)) ∧
      (min ce.length (frozenEnd ls - uint.nat ls.applying) = ce.length ∨
        ∃ e0, (nextUnstable ls).head? = some e0 ∧
          uint.nat ls.applying + 1 + min ce.length (frozenEnd ls - uint.nat ls.applying)
            = uint.nat e0.Index') := by
  refine ⟨?_, ?_⟩
  · unfold frozenRdy
    rw [List.take_take, Nat.min_eq_left (Nat.min_le_right _ _)]
    apply List.ext_getElem?
    intro j
    rw [List.getElem?_take, List.getElem?_take, List.getElem?_drop]
    split
    · rename_i hj
      have Hjc : j < ce.length := by omega
      rw [List.getElem?_eq_getElem Hjc]
      exact ce_log_at ls d ce Hdl Hpa Hcm Hcel Hag j _ (List.getElem?_eq_getElem Hjc)
    · rfl
  · by_cases Hm : min ce.length (frozenEnd ls - uint.nat ls.applying) = ce.length
    · exact Or.inl Hm
    · right
      unfold frozenEnd at Hm ⊢
      unfold logOffset at Hip
      have Hfe : min (uint.nat ls.committed) (uint.nat ls.inprogress - 1)
          = uint.nat ls.inprogress - 1 := by omega
      rw [Hfe] at Hm ⊢
      have Ho : ((uint.Z ls.inprogress - logOffset ls).toNat : Int)
          = uint.Z ls.inprogress - logOffset ls := Int.toNat_of_nonneg (by unfold logOffset; omega)
      unfold nextUnstable
      generalize (uint.Z ls.inprogress - logOffset ls).toNat = o at Ho ⊢
      unfold logOffset at Ho
      have Hof : o < ls.uents.length := by word
      rw [List.head?_drop, List.getElem?_eq_getElem Hof]
      refine ⟨_, rfl, ?_⟩
      have Hi := Hidx (ls.sents.length + o) _ (by
        rw [List.getElem?_append_right (by omega)]
        simp only [Nat.add_sub_cancel_left]
        exact List.getElem?_eq_getElem Hof)
      push_cast at Hi
      word

/-- The term of a committed entry `ce[k]` in raft's log, at its index `applying + k + 1`. -/
theorem cmt_termAt (ls : LogState) (d ce : List EntryM)
    (Hdl : d.length = uint.nat ls.applying)
    (Hpa : uint.nat ls.prev.index' ≤ uint.nat ls.applying)
    (Hcm : uint.Z ls.committed ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
      + (ls.uents.length : Int))
    (Hcel : uint.nat ls.applying + ce.length ≤ uint.nat ls.committed)
    (Hag : ∀ k e, (ls.sents ++ ls.uents)[k]? = some e →
      uint.nat ls.prev.index' + k < (d ++ ce).length →
      (d ++ ce)[uint.nat ls.prev.index' + k]? = some e)
    (k : Nat) (e : EntryM) (Hk : ce[k]? = some e) :
    plogTermAt ls.prev (ls.sents ++ ls.uents) (W64 ((uint.nat ls.applying + k + 1 : Nat) : Int))
      = some e.Term' := by
  have Hkl := (List.getElem?_eq_some_iff.mp Hk).1
  apply plogTermAt_lookup _ _ _ _ e (ce_log_at ls d ce Hdl Hpa Hcm Hcel Hag k e Hk)
  have : uint.Z (W64 ((uint.nat ls.applying + k + 1 : Nat) : Int))
      = ((uint.nat ls.applying + k + 1 : Nat) : Int) := by word
  rw [this]; push_cast; word

end lemmas

end EtcdGrove
end Perennial
