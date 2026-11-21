/- A newest-to-oldest prefix scan on the modern writer's segment layout. -/
module
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.snapshotPrefix

@[expose] public section
noncomputable section
namespace Perennial.EtcdGrove
open Iris Iris.BI Iris.ProofMode
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go.Semantics] [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

theorem wal.snapshotPrefix.wp_proof : wal.snapshotPrefix.spec (GF := GF) (hG := hG) := by
  intro P lg dir sl names dq first index h0 hlen hprobe
  wp_start as ⟨HP, Hsl⟩
  ihave %hl := ownSlice_len sl _ names $$ Hsl
  wp_auto
  ihave HI : iprop(∃ k : Int, "i" ∷ i_ptr ↦ W64 k ∗ "HP" ∷ P ∗ "Hsl" ∷ sl ↦*{dq} names ∗
      "%hk" ∷ ⌜-1 ≤ k ∧ k < sint.Z first⌝) $$ [i HP Hsl]
  · iexists sint.Z first - 1
    rw [show W64 (sint.Z first - 1) = first - W64 1 by word]
    iframe; ipureintro; omega
  wp_for HI
  have hkz : sint.Z (W64 k) = k := by word
  wp_if_destruct
  · have hpos : 0 ≤ k := by
      have h : sint.Z (W64 0) ≤ sint.Z (W64 k) := Hif
      rwa [hkz] at h
    have hn : k.toNat < names.length := by word
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word⟩)]
    obtain ⟨name, hname⟩ : ∃ name, names[k.toNat]? = some name := ⟨_, List.getElem?_eq_getElem hn⟩
    wp_apply wp_load_slice_index sl (sint.Z (W64 k)) names dq name (by word) $$ [Hsl] as Hsl
    · iframe; ipureintro; rw [hkz]; exact hname
    (try wp_auto)
    wp_apply hprobe k.toNat (by word) name hname $$ HP as %err HP
    cases err with
    | ok e =>
      wp_auto
      wp_for_post
      iapply HΦ
      iframe
    | nil =>
      wp_auto
      wp_for_post
      iframe
      iexists k - 1
      rw [show W64 (k - 1) = W64 k - W64 1 by word]
      iframe; ipureintro; omega
  · iapply HΦ; iframe

end Perennial.EtcdGrove
