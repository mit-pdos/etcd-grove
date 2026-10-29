/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/fits.lean`. Lean-first (no
Rocq counterpart). raft v3.7 (2026-10-16, stage R6b): the batch is a `[]*pb.Entry` (`entsPts`);
`es[0].GetIndex()` loads the first pointer and reads its index through the getter.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.fits
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]

theorem fits.wp_proof (wp_Entry_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG)) :
    fits.spec (GF := GF) (hG := hG) := by
  intro sl es dq
  wp_start as Hs
  ihave #Hpbinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  iunfold entsPts at Hs
  icases Hs with ⟨%ls, Hs, #Hb⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave %Hbl := entsBig_length $$ Hb
  ihave Hback : iprop(sl ↦*{dq} ls -∗ entsPts sl dq es) $$ []
  · iintro Hs; unfold entsPts; iexists ls; iframe Hs Hb
  wp_auto
  wp_if_destruct
  · iapply HΦ
    isplitl [Hs Hback]
    · iapply Hback $$ Hs
    ipureintro
    intro _ e0 He0
    have : es = [] := List.length_eq_zero_iff.mp (by rw [← Hbl, Hlen.1, Hif]; rfl)
    subst this; cases He0
  have Hne := Hif
  obtain ⟨e0, He0⟩ : ∃ e0, es[0]? = some e0 := by
    cases es with
    | nil => exfalso; apply Hne; simp at Hbl; subst Hbl; simp at Hlen; word
    | cons e _ => exact ⟨e, rfl⟩
  obtain ⟨l0, Hl0⟩ : ∃ l0, ls[0]? = some l0 := by
    cases ls with
    | nil =>
      exfalso
      have : es = [] := List.eq_nil_of_length_eq_zero (by simpa using Hbl.symm)
      subst this; simp at He0
    | cons l _ => exact ⟨l, rfl⟩
  have Hpos : 0 < sint.Z sl.len := by
    have := (List.getElem?_eq_some_iff.mp Hl0).1; obtain ⟨h1, h2⟩ := Hlen; word
  wp_if_destruct
  · rw [ite_eq_left (by word)]
    wp_apply wp_load_slice_index sl (sint.Z (W64 0)) ls dq l0 (by word) $$ [Hs] as Hs
    · iframe Hs; ipureintro; simpa using Hl0
    ihave #He0 := (BigSepL2.bigSepL2_lookup Hl0 He0) $$ Hb
    wp_apply wp_Entry_GetIndex.1 l0 DFrac.discard e0 $$ [$Hpbinit $He0] as -
    iapply HΦ
    isplitl [Hs Hback]
    · iapply Hback $$ Hs
    ipureintro
    intro Hd e0' He0'
    rw [List.head?_eq_getElem?, He0] at He0'
    cases He0'
    simp only [decide_eq_true_eq] at Hd
    obtain ⟨h1, h2⟩ := Hlen
    rw [← Hbl]
    word
  · iapply HΦ
    isplitl [Hs Hback]
    · iapply Hback $$ Hs
    ipureintro
    intro h; cases h

end proof

end kvreconf
end EtcdGrove
end Perennial
