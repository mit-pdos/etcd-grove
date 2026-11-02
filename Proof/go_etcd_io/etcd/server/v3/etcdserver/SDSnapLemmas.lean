/-
**The frozen entries, read** (stage P, track S-D, 2026-10-30): the persistence of `srvFrozenAt` and
`srvFrozenBelow`, and `Compact`'s premise at an index from `1` to the applied index from
`srvSnapState`'s frozen parts. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

instance srvFrozenAt_persistent_SD (γs : MemStorNames) (i : Nat) :
    Persistent (srvFrozenAt (GF := GF) γs i) := by
  unfold srvFrozenAt; infer_instance

instance srvFrozenBelow_persistent_SD (γs : MemStorNames) (n : Nat) :
    Persistent (srvFrozenBelow (GF := GF) γs n) := by
  unfold srvFrozenBelow; infer_instance

instance srvSnapStor_persistent_SD (ms : Loc) (γs : MemStorNames) (γr : ReadNames) (nk : GName) (ai at' : w64) :
    Persistent (srvSnapStor (GF := GF) ms γs γr nk ai at') := by
  unfold srvSnapStor; infer_instance

/-- **`Compact`'s entry premise** at an index `k` from `1` to the applied index `n`: frozen
(`srvFrozenAt` at `n`, `srvFrozenBelow` below it) or compacted. -/
theorem srvFrozen_get (γs : MemStorNames) (n k : Nat) (h1 : 1 ≤ k) (h2 : k ≤ n) :
    srvFrozenAt (GF := GF) γs n ∗ srvFrozenBelow γs n ⊢
      (∃ e, memLog γs k DFrac.discard [e]) ∨ memCompacted γs k := by
  iintro ⟨Ha, Hb⟩
  by_cases hk : k = n
  · subst hk
    iunfold srvFrozenAt at Ha
    icases Ha with (%h0 | ⟨%e, He⟩)
    · exfalso; omega
    · ileft; iexists e; iexact He
  · have hl : (List.range n)[k]? = some k := by
      rw [List.getElem?_range (by omega)]
    iunfold srvFrozenBelow at Hb
    iapply BigSepL.bigSepL_lookup
      (Φ := fun _ j => iprop((∃ e, memLog (GF := GF) γs j DFrac.discard [e]) ∨ memCompacted γs j)) hl
      $$ Hb

instance srvFrozenRange_persistent_SD (γs : MemStorNames) (lo hi : Nat) :
    Persistent (srvFrozenRange (GF := GF) γs lo hi) := by
  unfold srvFrozenRange srvFrozenAt; infer_instance

/-- (2026-10-31, the snapshot track: #11's S2) An index of the batch's frozen range, past `0`, has
a frozen entry. -/
theorem srvFrozenRange_at (γs : MemStorNames) (lo hi j : Nat) (h0 : 0 < j) (h1 : lo ≤ j)
    (h2 : j < hi) :
    srvFrozenRange (GF := GF) γs lo hi ⊢ ∃ e, memLog γs j DFrac.discard [e] := by
  iintro Hr
  have hl : (List.range' lo (hi - lo))[j - lo]? = some j := by
    rw [List.getElem?_range' (by omega)]; congr 1; omega
  iunfold srvFrozenRange at Hr
  ihave Ha := BigSepL.bigSepL_lookup (Φ := fun _ j => srvFrozenAt (GF := GF) γs j) hl $$ Hr
  iunfold srvFrozenAt at Ha
  icases Ha with (%h | Ha)
  · exfalso; omega
  · iexact Ha

/-- (2026-10-31, the snapshot track: #11's S2) **The frozen state moves with a batch**: frozen
through `ai`, and the batch's range `ai + 1 .. ai'` frozen (`raftAdvancedC`'s receipt), frozen
through `ai'`. Index `0` is compacted (`memCompacted`'s `c = 0`). -/
theorem srvSnapFrozen_extend (γs : MemStorNames) (ai ai' : Nat) (h : ai ≤ ai') :
    srvSnapFrozen (GF := GF) γs ai ∗ srvFrozenRange γs (ai + 1) (ai' + 1) ⊢
      srvSnapFrozen γs ai' := by
  have hB : □ (srvFrozenAt (GF := GF) γs ai ∗ srvFrozenBelow γs ai ∗
      srvFrozenRange γs (ai + 1) (ai' + 1)) ⊢ srvFrozenBelow γs ai' := by
    unfold srvFrozenBelow
    refine BigSepL.bigSepL_intro fun k j hk => ?_
    have hk' : k < ai' := by
      have := (List.getElem?_eq_some_iff.1 hk).1; simpa using this
    rw [List.getElem?_range hk', Option.some.injEq] at hk
    subst hk
    iintro #H
    icases H with ⟨#Ha, #Hb, #Hr⟩
    rcases Nat.lt_trichotomy k ai with hlt | heq | hgt
    · iapply BigSepL.bigSepL_lookup
        (Φ := fun _ j => iprop((∃ e, memLog (GF := GF) γs j DFrac.discard [e]) ∨ memCompacted γs j))
        (List.getElem?_range hlt) $$ Hb
    · subst heq
      iunfold srvFrozenAt at Ha
      icases Ha with (%h0 | ⟨%e, He⟩)
      · iright; iunfold memCompacted; ileft; ipureintro; exact h0
      · ileft; iexists e; iexact He
    · ileft
      iapply srvFrozenRange_at γs (ai + 1) (ai' + 1) k (by omega) (by omega) (by omega) $$ Hr
  iintro ⟨Hf, #Hr'⟩
  iunfold srvSnapFrozen at Hf
  icases Hf with ⟨#Ha, #Hb⟩
  iunfold srvSnapFrozen
  isplitr
  · by_cases hEq : ai' = ai
    · subst hEq; iexact Ha
    · iunfold srvFrozenAt; iright
      iapply srvFrozenRange_at γs (ai + 1) (ai' + 1) ai' (by omega) (by omega) (by omega) $$ Hr'
  iapply hB
  iframe Ha Hb Hr'

/-- (2026-10-31, the snapshot track: #11's S3) **The frozen state at the applied index, from the
log's frozen terms**: the applied log `L`, `ai` long, frozen from index `1` with its terms
(`raftAdvancedC`'s payload, a fresh start's) gives the storage frozen through `ai` and its entry at
`ai` of `L`'s last term. -/
theorem srv_frozen_of_terms (γs : MemStorNames) (L : List EntryModel) (ai at' : w64)
    (hn : uint.nat ai = L.length) (hlt : lastTermIs L at') :
    srvFrozenTerms (GF := GF) γs 1 L ⊢ srvSnapFrozen γs (uint.nat ai) ∗ srvFrozenTerm γs ai at' := by
  have hget : ∀ j m, L[j]? = some m → srvFrozenTerms (GF := GF) γs 1 L ⊢
      (∃ e : EntryM, memLog γs (j + 1) DFrac.discard [e] ∗ ⌜e.Term' = m.term⌝) ∨
        (⌜j + 1 < L.length⌝ ∗ memCompacted γs (j + 1)) := by
    intro j m hm
    unfold srvFrozenTerms
    refine (BigSepL.bigSepL_lookup
      (Φ := fun k m => iprop((∃ e : EntryM, memLog (GF := GF) γs (1 + k) DFrac.discard [e] ∗
        ⌜e.Term' = m.term⌝) ∨ (⌜k + 1 < L.length⌝ ∗ memCompacted γs (1 + k)))) hm).trans ?_
    rw [Nat.add_comm 1 j]
  have hB : □ srvFrozenTerms (GF := GF) γs 1 L ⊢ srvFrozenBelow γs (uint.nat ai) := by
    unfold srvFrozenBelow
    refine BigSepL.bigSepL_intro fun k j hk => ?_
    have hk' : k < uint.nat ai := by
      have := (List.getElem?_eq_some_iff.1 hk).1; simpa using this
    rw [List.getElem?_range hk', Option.some.injEq] at hk
    subst hk
    iintro #H
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · iright; iunfold memCompacted; ileft; ipureintro; exact h0
    · obtain ⟨m, hm⟩ : ∃ m, L[k - 1]? = some m :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      icases hget (k - 1) m hm $$ H with (⟨%e, #He, -⟩ | ⟨-, #Hc⟩)
      · ileft
        iexists e
        iExactEq He
        rw [show k - 1 + 1 = k by omega]
      · iright
        iExactEq Hc
        rw [show k - 1 + 1 = k by omega]
  iintro #H
  by_cases h0 : uint.nat ai = 0
  · iunfold srvSnapFrozen
    isplitr
    · isplitr
      · iunfold srvFrozenAt; ileft; ipureintro; exact h0
      iapply hB; iexact H
    iunfold srvFrozenTerm; ileft; ipureintro; exact h0
  obtain ⟨m, hm⟩ : ∃ m, L[uint.nat ai - 1]? = some m :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  icases hget (uint.nat ai - 1) m hm $$ H with (⟨%e, #He, %Ht⟩ | ⟨%hc, -⟩)
  rotate_left
  · exfalso; omega
  rw [show uint.nat ai - 1 + 1 = uint.nat ai by omega] at *
  have hmt : m.term = at' := by
    rcases hlt with hL | hL
    · subst hL; simp at hn; omega
    rw [List.getLast?_eq_getElem?, show L.length - 1 = uint.nat ai - 1 by omega, hm] at hL
    simpa using hL
  iunfold srvSnapFrozen
  isplitr
  · isplitr
    · iunfold srvFrozenAt; iright; iexists e; iexact He
    iapply hB; iexact H
  iunfold srvFrozenTerm; iright; iexists e
  iframe He
  ipureintro; rw [Ht, hmt]

end lemmas

end EtcdGrove
end Perennial
