/-
Lean-first (no Rocq counterpart). #33 parity B1, driver group E (S4's `DrainStore`): **`node.drain`'s write** (`storeSave(p.hs, p.ents)`'s `MemoryStorage.Append`),
between raft's storage vocabulary and the `MemoryStorage`'s, through the node's bridge
(`antStorBridge`, `nodeStor`): a `Ready` without a snapshot hands out the right to write its batch
(`appendRight`), which is `MemoryStorage.Append`'s precondition at the batch's first index
(`append_pre`); the batch written is the receipt `rawNode_appended` takes, with no frozen prefix
(`append_post`, `a = []`: the harness never freezes, its storage is the node goroutine's alone).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.AntStorage
public import Proof.go_etcd_io.raft.v3.ApiVocab

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]

/-- **The right to write a batch is `Append`'s precondition** at the batch's first index `k`. -/
theorem append_preB1 (st : Storage) (γs : MemStorNames) (es : List EntryM) :
    antStorBridge (GF := GF) st γs ∗ appendRight st es ⊢
      ∃ (k : Nat) (old : List EntryM), ⌜∀ e0 ∈ es.head?, k = uint.nat e0.Index'⌝ ∗
        (if es = [] then emp else memLog γs k (DFrac.own 1) old ∗ memEnd γs (k + old.length)) := by
  iintro ⟨#Hb, Ha⟩
  iunfold appendRight at Ha
  icases Ha with (%He | ⟨%e0, %old, %Hh, Hl, He⟩)
  · iexists 0, []
    subst He
    simp only [List.head?_nil, Option.mem_def, reduceCtorEq, false_implies, implies_true,
      ↓reduceIte]
    ipureintro; trivial
  · iexists uint.nat e0.Index', old
    have hne : es ≠ [] := by intro h; rw [h] at Hh; cases Hh
    simp only [hne, ↓reduceIte]
    isplitr
    · ipureintro
      intro e he
      rw [Hh] at he
      cases he; rfl
    ihave Hl := antStorBridge_log_to st γs _ _ _ $$ Hb Hl
    ihave He := antStorBridge_end_to st γs _ $$ Hb He
    iframe Hl He

/-- **The batch written is the receipt of the right** (no frozen prefix). -/
theorem append_postB1 (st : Storage) (γs : MemStorNames) (es : List EntryM) (k : Nat)
    (hk : ∀ e0 ∈ es.head?, k = uint.nat e0.Index') :
    antStorBridge (GF := GF) st γs ∗
        (if es = [] then emp else memLog γs k (DFrac.own 1) es ∗ memEnd γs (k + es.length)) ⊢
      appendReceipt st es [] := by
  iintro ⟨#Hb, Hw⟩
  iunfold appendReceipt
  by_cases hne : es = []
  · ileft; ipureintro; exact hne
  · iright
    simp only [hne, ↓reduceIte]
    icases Hw with ⟨Hl, He⟩
    obtain ⟨e0, he0⟩ : ∃ e0, es.head? = some e0 := by
      cases es with
      | nil => exact absurd rfl hne
      | cons x xs => exact ⟨x, rfl⟩
    have hk' : k = uint.nat e0.Index' := hk e0 he0
    subst hk'
    iexists e0, es
    isplitr
    · ipureintro; exact ⟨he0, rfl⟩
    ihave Hl := antStorBridge_log_of st γs _ _ _ $$ Hb Hl
    ihave He := antStorBridge_end_of st γs _ $$ Hb He
    ihave Hn : storLog st (uint.nat e0.Index') DFrac.discard ([] : List EntryM) $$ []
    · iapply StorageModel.storLog_nil
    simp only [List.length_nil, Nat.add_zero]
    iframe Hn Hl He

end proof

end AntHarness
end EtcdGrove
end Perennial
