/-
Lean-first (no Rocq counterpart).

# Appending a `Ready`'s entries, without a snapshot (2026-10-30, kvreconf's `run`)

`append_none_pre`: the range `readySnap` lends (`appendRight`, at the wrapper's interface) as the
`MemoryStorage`'s, which `Storage.wp_Append` takes. `append_none_post`: after the append, the batch's
committed prefix frozen (`batch_freeze`), which gives `frozenTo` past the `Ready`'s committed entries
and `Advance`'s receipt (`advReceipt none`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.RunBatch

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section append
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KvrStor GF]

attribute [local instance] kvrStorageModel

theorem append_none_pre (st ms : Loc) (γs : MemStorNames) (es : List EntryM) :
    ⊢ kvrStorRec (GF := GF) st ms γs -∗ appendRight (kvrStorIface st) es -∗
      ∃ (k : Nat) (old : List EntryM), ⌜∀ e0, es.head? = some e0 → k = uint.nat e0.Index'⌝ ∗
        (if es = [] then emp else memLog γs k (DFrac.own 1) old ∗ memEnd γs (k + old.length)) := by
  iintro #Hrec Happ
  iunfold appendRight at Happ
  icases Happ with (%He | ⟨%e0, %old, %Hh, Hl, He⟩)
  · subst He
    iexists 0, []
    simp only [if_true]
    isplitr
    · ipureintro; intro e h; cases h
    itrivial
  · iexists uint.nat e0.Index', old
    have hne : es ≠ [] := by intro h; subst h; cases Hh
    simp only [if_neg hne]
    isplitr
    · ipureintro; intro e h; rw [Hh] at h; cases h; rfl
    ihave Hl := kvrStorLog_to st ms γs _ _ _ $$ Hrec Hl
    ihave He := kvrStorEnd_to st ms γs _ $$ Hrec He
    iframe Hl He

theorem append_none_post (st ms : Loc) (γs : MemStorNames) (c : Nat) (D ce : List LogEntry)
    (es : List EntryM) (k : Nat) (Hc : c ≤ D.length)
    (Hin : ∀ e0, es.head? = some e0 → ∀ (j : Nat) (e : LogEntry), ce[j]? = some e →
      uint.nat e0.Index' ≤ D.length + 1 + j →
      Option.map LogEntry.ofEntryM es[D.length + 1 + j - uint.nat e0.Index']? = some e)
    (Hidx : ∀ e0, es.head? = some e0 → ∀ j e, es[j]? = some e →
      uint.nat e.Index' = uint.nat e0.Index' + j)
    (Hk : ∀ e0, es.head? = some e0 → k = uint.nat e0.Index') :
    ⊢ kvrStorRec (GF := GF) st ms γs -∗ frozenTo γs c D -∗
      ceFrozen (kvrStorIface st) D.length (LogEntry.toEntries ce D.length) es -∗
      (if es = [] then emp else memLog γs k (DFrac.own 1) es ∗ memEnd γs (k + es.length)) ==∗
      frozenTo γs c (D ++ ce) ∗ advReceipt (kvrStorIface st) (D ++ ce).length es none := by
  iintro #Hrec #Hf #Hcf Hb
  iunfold ceFrozen at Hcf
  icases Hcf with ⟨%m0, #Hm0, %Hm⟩
  ihave #Hm0 := kvrStorLog_to st ms γs _ _ _ $$ Hrec Hm0
  have Hm' : m0 = ce.length ∨ ∃ e0, es.head? = some e0 ∧ D.length + 1 + m0 = uint.nat e0.Index' := by
    rw [kvr_toEntries_length] at Hm; exact Hm
  imod batch_freeze γs c D ce es m0 k Hc Hm' Hin Hidx Hk $$ Hf Hm0 Hb with ⟨#Hf', %a, %Ha, Hr⟩
  imodintro
  iframe Hf'
  unfold advReceipt
  iexists a
  isplitl
  · unfold appendReceipt
    by_cases he : es = []
    · ileft; ipureintro; exact he
    · iright
      simp only [if_neg he]
      icases Hr with ⟨#Ha', Hb', He'⟩
      obtain ⟨e0, he0⟩ : ∃ e0, es.head? = some e0 := by
        cases es with
        | nil => exact absurd rfl he
        | cons x xs => exact ⟨x, rfl⟩
      iexists e0, es.drop a.length
      isplitr
      · ipureintro
        obtain ⟨t, rfl⟩ := Ha.2
        refine ⟨he0, ?_⟩
        simp
      rw [← Hk e0 he0]
      ihave Ha' := kvrStorLog_of st ms γs _ _ _ $$ Hrec Ha'
      ihave Hb' := kvrStorLog_of st ms γs _ _ _ $$ Hrec Hb'
      ihave He' := kvrStorEnd_of st ms γs _ $$ Hrec He'
      iframe Ha' Hb' He'
  · ipureintro
    intro hne e0 he0
    have := Ha.1 hne
    rw [Hk e0 he0] at this
    exact this

end append

end kvreconf
end EtcdGrove
end Perennial
