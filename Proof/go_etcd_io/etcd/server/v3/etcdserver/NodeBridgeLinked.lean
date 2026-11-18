/-
The `MemoryStorage` meets `isRNMemStor` at raft's linked `MemoryStorage.wp_Append`
(`isRNMemStor_of_memstorage`): the one discharge of `NodeBridge.lean` over a linked result, moved
out of it (2026-11-18) so that `NodeBridge.lean`, which the server's invariants import, imports no
linked result (CLAUDE.md, "Import tiers").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NodeBridge
public import Proof.go_etcd_io.raft.v3.Linked

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open RaftLink


open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section bridge
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The `MemoryStorage` meets `isRNMemStor`** (raft's linked `MemoryStorage.wp_Append`, under the
storage's lock invariant `memStorLock`; 2026-10-30, the repair: until then raft's `memStorage_Append`): the `Ready`'s right to append, with the index bound `rnAppendRight`
carries (`rnLogFits`'s), is the receipt `Advance` takes. -/
theorem isRNMemStor_of_memstorage (γ : RNNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ rnMemStorReg γ ∗
      memStorLock γ.ms γ.γs ⊢
      isRNMemStor γ γ.ms := by
  letI : MemStorReg GF := ⟨γ.reg⟩
  iintro ⟨#Hpkg, #Hreg, #Hlock⟩
  iunfold isRNMemStor
  iintro !> %sl %es %Φ !> ⟨#Hents, Hright⟩ HΦ
  iunfold rnAppendRight at Hright
  icases Hright with ⟨Hright, %Hfit⟩
  obtain ⟨Hfits, Hcons⟩ := Hfit
  ihave #Hpts : entsPtsZ γ.γs.sz sl DFrac.discard (es.map EntryModel.toM) $$ []
  · iapply entsPtsZ_true $$ Hents
  iunfold appendRight at Hright
  icases Hright with (%Hnil | ⟨%e0, %old, %Hh, Hl, He⟩)
  · -- nothing to append
    have hes : es = [] := by simpa using Hnil
    subst hes
    wp_apply (MemoryStorage.wp_Append γ.ms γ.γs 0 [] [] sl DFrac.discard
        (fun _ _ h => by cases h) (by simp)) $$ [] as -
    · iframe #
      simp only [List.map_nil, ite_true]
      iframe Hpts
    iapply HΦ
    iunfold rnAppendReceipt
    iunfold appendReceipt
    ileft; ipureintro; rfl
  · obtain ⟨x, hx, rfl⟩ : ∃ x, es.head? = some x ∧ e0 = x.toM := by
      rw [List.head?_map] at Hh
      cases hh : es.head? with
      | none => rw [hh] at Hh; cases Hh
      | some x => rw [hh] at Hh; cases Hh; exact ⟨x, rfl, rfl⟩
    have hne : es.map EntryModel.toM ≠ [] := by
      intro h; rw [List.map_eq_nil_iff] at h; subst h; cases hx
    have hidx : ∀ (j : Nat) (e : EntryM), (es.map EntryModel.toM)[j]? = some e →
        uint.nat e.Index' = uint.nat x.toM.Index' + j := by
      intro j e he
      rw [List.getElem?_map] at he
      cases hj : es[j]? with
      | none => rw [hj] at he; cases he
      | some y =>
        rw [hj] at he; cases he
        exact Hcons x hx j y hj
    have hfit : uint.nat x.toM.Index' + (es.map EntryModel.toM).length ≤ 2 ^ 61 := by
      have := Hfits x hx
      simp only [List.length_map]
      show uint.nat x.index + es.length ≤ 2 ^ 61
      have : (uint.nat x.index : Int) = uint.Z x.index := by word
      omega
    ihave Hl := memStorLog_to γ.ms γ.γs _ _ _ $$ Hreg Hl
    ihave He := memStorEnd_to γ.ms γ.γs _ $$ Hreg He
    wp_apply (MemoryStorage.wp_Append γ.ms γ.γs (uint.nat x.toM.Index') old
        (es.map EntryModel.toM) sl DFrac.discard hidx hfit) $$ [Hl He] as ⟨-, Hpost⟩
    · iframe #
      simp only [ite_eq_right hne]
      iframe Hl He
    simp only [ite_eq_right hne]
    icases Hpost with ⟨Hl, He⟩
    iapply HΦ
    iunfold rnAppendReceipt
    iunfold appendReceipt
    iright
    iexists x.toM, es.map EntryModel.toM
    isplitr
    · ipureintro
      refine ⟨?_, rfl⟩
      rw [List.head?_map, hx]; rfl
    ihave #Hnil := memLog_nil γ.γs (uint.nat x.toM.Index') DFrac.discard
    ihave #Hnil' := memStorLog_of γ.ms γ.γs _ _ _ $$ Hreg Hnil
    ihave Hl := memStorLog_of γ.ms γ.γs _ _ _ $$ Hreg Hl
    ihave He := memStorEnd_of γ.ms γ.γs _ $$ Hreg He
    simp only [List.length_nil, Nat.add_zero]
    rw [show x.toM.Index' = x.index from rfl]
    iframe Hnil' Hl He

end bridge

end EtcdGrove
end Perennial
