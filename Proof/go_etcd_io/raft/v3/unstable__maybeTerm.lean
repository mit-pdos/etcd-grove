/-
Port of election_proof/proof_unstable__maybeTerm.v.
-/
module

public import Spec.go_etcd_io.raft.v3.unstable__maybeTerm
public import Spec.go_etcd_io.raft.v3.unstable__maybeLastIndex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem unstable.maybeTerm.wp_proof
    (wp_unstable_maybeLastIndex : unstable.maybeLastIndex.spec (GF := GF) (hG := hG)) :
    unstable.maybeTerm.spec (GF := GF) (hG := hG) := by
  intro u us i Hsoff Hnw
  wp_start as H
  iNamed H
  open_unstable
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hents
  wp_if_destruct
  · rcases snap_some_or_none us.snap with ⟨sid, Hs⟩ | Hs
    · -- below `offset`, with a snapshot pending: its term at its index
      icases ownSnap_of_eq_some Hs $$ Hsnap with ⟨%sv, #Hsv, %Hmeta, -⟩
      ihave %Hnn := typedPointsto_not_null $$ Hsv
      obtain ⟨Hidx, Htm⟩ := Hmeta
      simp only [Hnn, decide_false]
      iStructNamedSuffix Hsv "_s"
      iStructNamedSuffix Metadata_s "_m"
      wp_auto
      rw [Hidx]
      wp_if_destruct
      · iapply HΦ
        isplitl
        · close_unstable
        ipureintro
        refine ⟨⟨fun _ => Or.inr ⟨sid, Hs, rfl⟩, fun _ => rfl⟩, fun _ => ?_⟩
        exact Or.inr ⟨sid, Hs, rfl, Htm⟩
      · iapply HΦ
        isplitl
        · close_unstable
        ipureintro
        refine ⟨⟨fun h => (nomatch h), ?_⟩, fun h => (nomatch h)⟩
        rintro (Hc | ⟨sid', Hc, Hi⟩)
        · omega
        · rw [Hs] at Hc; cases Hc; exact absurd Hi.symm Hif
    · ihave %Hns := ownSnap_of_eq_none Hs $$ Hsnap
      simp only [decide_eq_true Hns]
      wp_auto
      iapply HΦ
      isplitl
      · close_unstable
      ipureintro
      refine ⟨⟨fun h => (nomatch h), ?_⟩, fun h => (nomatch h)⟩
      rintro (Hc | ⟨sid', Hc, _⟩)
      · omega
      · rw [Hs] at Hc; cases Hc
  · -- at or above `offset`, a pending snapshot's index is not `i`
    have Hnsnap : ¬ ∃ sid, us.snap = some sid ∧ i = sid.index' := by
      rintro ⟨sid, Hs, rfl⟩
      have := Hsoff sid Hs
      omega
    wp_apply wp_unstable_maybeLastIndex u us Hnw
        $$ [Hu Hents Hents_cap] as %last %ok ⟨Hun, %Hok1, %Hok2⟩
    · close_unstable
    open_unstable_again
    ihave %Hlen := ownSlice_len $$ Hents
    by_cases He : us.ents = []
    · obtain ⟨Hok, Hlast⟩ := Hok1 He
      subst Hok
      rcases snap_some_or_none us.snap with ⟨sid, Hs⟩ | Hs
      · -- only the snapshot: `last` is its index, below `i`
        rw [decide_eq_true (by simp [Hs])]
        rw [Hlast sid Hs]
        wp_auto
        have := Hsoff sid Hs
        wp_if_destruct
        · iapply HΦ
          isplitl
          · close_unstable
          ipureintro
          refine ⟨⟨fun h => (nomatch h), ?_⟩, fun h => (nomatch h)⟩
          rintro (Hc | Hc)
          · simp only [He, List.length_nil] at Hc; omega
          · exact absurd Hc Hnsnap
        · exfalso; apply Hnsnap; refine ⟨sid, Hs, ?_⟩; word
      · rw [decide_eq_false (by simp [Hs])]
        wp_auto
        iapply HΦ
        isplitl
        · close_unstable
        ipureintro
        refine ⟨⟨fun h => (nomatch h), ?_⟩, fun h => (nomatch h)⟩
        rintro (Hc | Hc)
        · simp only [He, List.length_nil] at Hc; omega
        · exact absurd Hc Hnsnap
    · obtain ⟨Hokt, Hlast⟩ := Hok2 He
      subst Hokt
      wp_auto
      wp_if_destruct
      · iapply HΦ
        isplitl
        · close_unstable
        ipureintro
        refine ⟨⟨fun h => (nomatch h), ?_⟩, fun h => (nomatch h)⟩
        rintro (Hc | Hc)
        · omega
        · exact absurd Hc Hnsnap
      · have Hbnd : 0 ≤ sint.Z (i - us.offset) ∧
            sint.Z (i - us.offset) < sint.Z uv.entries'.len := by
          constructor <;> word
        simp only [Hbnd, and_self, ↓reduceIte]
        have Hk : (sint.Z (i - us.offset)).toNat = (uint.Z i - uint.Z us.offset).toNat := by
          word
        have Hlt : (sint.Z (i - us.offset)).toNat < us.ents.length := by word
        obtain ⟨e, He_lk⟩ : ∃ e, us.ents[(sint.Z (i - us.offset)).toNat]? = some e :=
          ⟨_, List.getElem?_eq_getElem Hlt⟩
        icases Hents with #Hents
        icases ownSlice_elem_acc (sint.Z (i - us.offset)) e uv.entries' _ us.ents Hbnd.1 He_lk
          $$ Hents with ⟨#He, -⟩
        iStructNamedSuffix He "_e"
        wp_auto
        iapply HΦ
        isplitl
        · close_unstable
        ipureintro
        refine ⟨⟨fun _ => Or.inl ⟨by omega, by omega⟩, fun _ => rfl⟩, fun _ => ?_⟩
        refine Or.inl ⟨⟨by omega, by omega⟩, e, ?_, rfl⟩
        rw [← Hk]; exact He_lk

end proof

end EtcdGrove
end Perennial
