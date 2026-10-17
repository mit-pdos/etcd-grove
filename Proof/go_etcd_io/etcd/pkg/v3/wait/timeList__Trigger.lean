/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/wait/timeList__Trigger.lean`. Lean-first (no Rocq counterpart); the
request path's unit 4b.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.wait.timeList__Trigger
public import Spec.go_etcd_io.etcd.pkg.v3.wait.deadlineHeap__pop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3 waitHeap

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.wait.Assumptions]

theorem wait.timeList.Trigger.wp_proof (hPop : wait.deadlineHeap.pop.spec (GF := GF) (hG := hG)) :
    wait.timeList.Trigger.spec (GF := GF) (hG := hG) := by
  intro tl P d
  wp_start as ⟨#Htl, #HPd⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold isTimeList at Htl
  icases Htl with ⟨%mref, #Hm, #Hmu, #Hmono, #Hcl⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold timeListR at HR
  icases HR with ⟨%last, %M, %hs, %xs, Hlast, HM, #Hlastp, Hchs, Hh, Hs, Hcap, %Hok⟩
  obtain ⟨Hheap, Hmatch, -, Hlen⟩ := Hok
  (try wp_auto)
  ihave HI : (∃ (M : GMap w64 Loc) (hs : GoSlice) (xs : List w64), "HM" ∷ ownMap mref (DFrac.own 1) M ∗
      "Hchs" ∷ ([∗map] t ↦ c ∈ M, ∃ γ : ChanNames, ownBroadcastChan c γ (P t) Broadcast.Pending) ∗
      "Hh" ∷ tlHeapAddr tl ↦ hs ∗ "Hs" ∷ hs ↦* xs ∗ "Hcap" ∷ ownSliceCap w64 hs (DFrac.own 1) ∗
      "%Hok" ∷ ⌜heapOk xs ∧ heapMatch xs M ∧ xs.length < 2 ^ 62⌝ : IProp GF) $$ [HM Hchs Hh Hs Hcap]
  · iexists M, hs, xs; iframe; ipureintro; exact ⟨Hheap, Hmatch, Hlen⟩
  wp_for HI
  obtain ⟨Hheap, Hmatch, Hlen⟩ := Hok
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  -- leaving the loop: every deadline left is above `d`
  have Hexit : ∀ (M : GMap w64 Loc) (xs : List w64), heapOk xs → heapMatch xs M → xs.length < 2 ^ 62 →
      (xs = [] ∨ ∃ x0, xs[0]? = some x0 ∧ uint.Z d < uint.Z x0) → tlHeapOk xs M d := by
    intro M xs h1 h2 h3 h4
    refine ⟨h1, h2, ?_, h3⟩
    rcases h4 with rfl | ⟨x0, hx0, hlt⟩
    · intro k hk; cases hk
    · intro k hk; exact Int.lt_of_lt_of_le hlt (heapOk_min h1 hx0 k hk)
  wp_if_destruct
  · have H0b : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z hs.len := by constructor <;> word
    (try wp_auto)
    try simp only [H0b, _root_.and_self, ↓reduceIte]
    list_elem xs 0 as x0
    wp_apply wp_load_slice_index hs _ xs _ x0 H0b.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hx0_lookup
    (try wp_auto)
    wp_if_destruct
    · -- `t := tl.h.pop()`
      wp_apply hPop (tlHeapAddr tl) hs xs $$ [$Hh $Hs $Hcap] as %t ⟨%hs', %xs', Hh, Hs, Hcap, %Hpop⟩
      · iframe #; ipureintro; exact ⟨Hheap, by word, by omega⟩
      obtain ⟨Ht0, -, Hheap', Hperm'⟩ := Hpop
      rw [Hx0_lookup] at Ht0; cases Ht0
      have Hle : uint.Z x0 ≤ uint.Z d := by
        by_cases h : uint.Z x0 ≤ uint.Z d
        · exact h
        · simp [h, intoVal_eq_iff] at Hif
      have Hx0mem : x0 ∈ xs := List.mem_of_getElem? Hx0_lookup
      obtain ⟨ch, Hch⟩ := heapMatch_lookup Hmatch Hx0mem
      (try wp_auto)
      wp_apply wp_map_lookup1 $$ [$HM] as HM
      rw [show M !! x0 = some ch from Hch]
      simp only [Option.getD_some]
      icases (BigSepM.bigSepM_delete (Φ := fun t c =>
          iprop(∃ γ : ChanNames, ownBroadcastChan c γ (P t) Broadcast.Pending)) Hch).1 $$ Hchs
        with ⟨⟨%γ, Hb⟩, Hchs⟩
      ihave #HPk : iprop(□ P x0) $$ []
      · iunfold waitMono at Hmono
        imodintro
        iapply Hmono $$ %d %x0 %Hle HPd
      (try wp_auto)
      wp_apply wp_broadcast_chan_close ch γ (P x0) $$ [$Hb] as -
      · iexact HPk
      (try wp_auto)
      wp_apply wp_mapDelete $$ [$HM] as HM
      (try wp_auto)
      wp_for_post
      iframe
      iexists _, hs', xs'
      iframe
      ipureintro
      have Hlen' : xs'.length < 2 ^ 62 := by
        have := Hperm'.length_eq; simp only [List.length_cons] at this; omega
      exact ⟨Hheap', heapMatch_delete Hmatch Hperm', Hlen'⟩
    · have hgt : ¬ uint.Z x0 ≤ uint.Z d := by
        intro h; apply Hif; simp [h]
      rw [decide_eq_false hgt]
      simp only [Bool.false_eq_true, ↓reduceIte]
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hlast HM Hchs Hh Hs Hcap]
      · inext; iunfold timeListR; iexists d, M, hs, xs; iframe; iframe #
        ipureintro
        exact Hexit M xs Hheap Hmatch Hlen (Or.inr ⟨x0, Hx0_lookup, by omega⟩)
      (try wp_auto)
      iapply HΦ
      itrivial
  · have Hnil : xs = [] := by
      apply List.eq_nil_of_length_eq_zero; word
    (try wp_auto)
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hlast HM Hchs Hh Hs Hcap]
    · inext; iunfold timeListR; iexists d, M, hs, xs; iframe; iframe #
      ipureintro
      exact Hexit M xs Hheap Hmatch Hlen (Or.inl Hnil)
    (try wp_auto)
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
