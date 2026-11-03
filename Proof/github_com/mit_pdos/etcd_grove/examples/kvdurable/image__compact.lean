/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/image__compact.lean`. Lean-first
(no Rocq counterpart): at or below the log's start, `ErrCompacted`; past it (and at most the last
index, the premise), the term of the entry at `i` read, the entries after it sliced off.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.image__compact
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetTerm
public import Proof.go_etcd_io.raft.v3.LemmasEnts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem image.compact.wp_proof (wp_GetTerm : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG)) :
    image.compact.spec (GF := GF) (hG := hG) := by
  intro p I i eco Hle
  wp_start as ⟨Himg, #Herr⟩
  iunfold ownImage at Himg
  icases Himg with ⟨%hsp, %sp, %es, Himg⟩
  iNamed Himg
  wp_auto
  ihave %Hlen := entsPts_len $$ HentsO
  wp_if_destruct
  · -- at or below the log's start: `ErrCompacted`
    have Hst : imgCompactStale I i := by unfold imgCompactStale; word
    iapply HΦ
    rw [ite_eq_left Hst]
    isplitr
    · ipureintro; rfl
    iunfold ownImage
    iexists hsp, sp, es
    iframe # ∗
    ipureintro; exact Hwf
  -- past it, at most the last index
  have Hst : ¬ imgCompactStale I i := by unfold imgCompactStale; word
  have Hgt : uint.nat I.prev < uint.nat i := by word
  wp_if_destruct
  · exfalso
    have : uint.Z (I.prev + es.len) = uint.Z I.prev + I.ents.length := by word
    word
  obtain ⟨e, He⟩ : ∃ e, I.ents[uint.nat i - uint.nat I.prev - 1]? = some e :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  ihave #HentsO' := HentsO
  iunfold entsRO at HentsO'
  iunfold entsPts at HentsO'
  icases HentsO' with ⟨%ls, #Hls, #Hbig⟩
  ihave %Hbl := entsBig_length $$ Hbig
  icases entsBig_lookup ls I.ents _ e He $$ Hbig with ⟨%l, %Hl, #Hel⟩
  have Hk : sint.Z (i - I.prev - W64 1) = uint.Z i - uint.Z I.prev - 1 := by word
  rw [ite_eq_left ⟨by word, by word⟩]
  wp_apply wp_load_slice_index es (sint.Z (i - I.prev - W64 1)) ls DFrac.discard l (by word)
    $$ [Hls] with -
  · iframe Hls; ipureintro
    rw [show (sint.Z (i - I.prev - W64 1)).toNat = uint.nat i - uint.nat I.prev - 1 by word]
    exact Hl
  wp_apply wp_GetTerm.1 l DFrac.discard e $$ [Hel] with -
  · iframe Hel
  try wp_auto
  ihave %Hwf1 := ownSlice_wf $$ Hls
  rw [ite_eq_left ⟨by word, by word, Hwf1.2⟩]
  icases (ownSlice_slice (i - I.prev) es.len es DFrac.discard ls ⟨by word, by word, by word⟩).1
    $$ Hls with ⟨-, #Hrest, -⟩
  ihave #Hb2 := entsBig_subslice (sint.nat (i - I.prev)) (sint.nat es.len) ls I.ents $$ Hbig
  have HE : subslice (sint.nat (i - I.prev)) (sint.nat es.len) I.ents =
      I.ents.drop (uint.nat i - uint.nat I.prev) := by
    simp only [subslice]
    rw [List.take_of_length_le (by word)]
    congr 1; word
  have Hterm : imgTermAt I i = e.Term' := by
    unfold imgTermAt; rw [ite_eq_right (by omega), He]; rfl
  wp_auto
  iapply HΦ
  rw [ite_eq_right Hst]
  isplitr
  · ipureintro; rfl
  iunfold ownImage
  iexists hsp, sp, (slice.slice es Loc (i - I.prev) es.len)
  simp only [imgCompact, Hterm]
  iframe # ∗
  isplitr
  · iunfold entsRO; iunfold entsPts
    iexists subslice (sint.nat (i - I.prev)) (sint.nat es.len) ls
    rw [← HE]
    iframe Hrest Hb2
  ipureintro
  simp only [List.length_drop]
  omega

end proof

end kvdurable
end EtcdGrove
end Perennial
