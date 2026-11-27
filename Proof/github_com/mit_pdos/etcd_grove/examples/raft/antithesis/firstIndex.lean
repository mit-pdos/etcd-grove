/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/firstIndex.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.firstIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex

@[expose] public section

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem firstIndex.wp_proof (wp_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG)) :
    firstIndex.spec (GF := GF) (hG := hG) := by
  intro sl dq els es
  wp_start as ⟨Hsl, #Hents⟩
  ihave %Hl := ownSlice_len $$ Hsl
  ihave %Hl2 := BigSepL2.bigSepL2_length $$ Hents
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_auto
  wp_if_destruct
  · have hes : es = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [← Hl2, Hl.1, Hif]; rfl
    subst hes
    rw [show firstIdx [] = W64 0 from rfl]
    iapply HΦ
    iframe
    iexact Hents
  · obtain ⟨l, ls, rfl⟩ : ∃ l ls, els = l :: ls := by
      cases els with
      | nil => exfalso; apply Hif; have : sint.nat sl.len = 0 := by rw [← Hl.1]; rfl
               word
      | cons l ls => exact ⟨l, ls, rfl⟩
    obtain ⟨e, es', rfl⟩ : ∃ e es', es = e :: es' := by
      cases es with
      | nil => simp at Hl2
      | cons e es' => exact ⟨e, es', rfl⟩
    ihave #He := BigSepL2.bigSepL2_lookup (i := 0) rfl rfl $$ Hents
    rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len by
      have : sint.Z sl.len ≠ 0 := fun h => Hif (by word)
      constructor <;> word)]
    wp_apply wp_load_slice_index sl (sint.Z (W64 0)) (l :: ls) dq l (by decide) $$ [Hsl] as Hsl
    · iframe; ipureintro; rfl
    wp_apply wp_GetIndex.1 l DFrac.discard e $$ [$Hpb $He] as -
    try wp_auto
    rw [show firstIdx (e :: es') = e.Index' from rfl]
    iapply HΦ
    iframe
    iexact Hents

end proof

end AntHarness
end EtcdGrove
end Perennial
