/-
Port of election_proof/proof_unstable__maybeTerm.v.
-/
import EtcdGrove.Raft.Spec.unstable__maybeTerm
import EtcdGrove.Raft.Spec.unstable__maybeLastIndex

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem unstable.maybeTerm.wp_proof
    (wp_unstable_maybeLastIndex : unstable.maybeLastIndex.spec (GF := GF) (hG := hG)) :
    unstable.maybeTerm.spec (GF := GF) (hG := hG) := by
  intro u us
  obtain ⟨uents, off, ip, snap⟩ := us
  intro i Hsoff Hnw
  dsimp only at Hsoff Hnw
  wp_start as H
  iNamed H
  open_unstable
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hents
  wp_if_destruct
  · cases snap with
    | some sid =>
      -- below `offset`, with a snapshot pending: its term at its index
      icases (ownSnap_Some _ _).1 $$ Hsnap with ⟨%sv, #Hsv, %Hmeta, -⟩
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
        refine ⟨⟨fun _ => Or.inr ⟨sid, rfl, rfl⟩, fun _ => rfl⟩, fun _ => ?_⟩
        exact Or.inr ⟨sid, rfl, rfl, Htm⟩
      · iapply HΦ
        isplitl
        · close_unstable
        ipureintro
        refine ⟨⟨fun h => (nomatch h), ?_⟩, fun h => (nomatch h)⟩
        rintro (Hc | ⟨sid', Hc, Hi⟩)
        · omega
        · cases Hc; exact absurd Hi.symm Hif
    | none =>
      ihave %Hns := (ownSnap_None _).1 $$ Hsnap
      simp only [decide_eq_true Hns]
      wp_auto
      iapply HΦ
      isplitl
      · close_unstable
      ipureintro
      refine ⟨⟨fun h => (nomatch h), ?_⟩, fun h => (nomatch h)⟩
      rintro (Hc | ⟨sid', Hc, _⟩)
      · omega
      · cases Hc
  · -- at or above `offset`, a pending snapshot's index is not `i`
    have Hnsnap : ¬ ∃ sid, snap = some sid ∧ i = sid.index' := by
      rintro ⟨sid, Hs, rfl⟩
      have := Hsoff sid Hs
      omega
    wp_apply wp_unstable_maybeLastIndex u ⟨uents, uv.offset', uv.offsetInProgress', snap⟩ Hnw
        $$ [Hu Hents Hents_cap] as %last %ok ⟨Hun, %Hok1, %Hok2⟩
    · close_unstable
    dsimp only at Hok1 Hok2
    open_unstable_again
    ihave %Hlen := ownSlice_len $$ Hents
    by_cases He : uents = []
    · obtain ⟨Hok, Hlast⟩ := Hok1 He
      subst Hok
      subst He
      cases snap with
      | some sid =>
        -- only the snapshot: `last` is its index, below `i`
        simp only [ne_eq, reduceCtorEq, not_false_eq_true, decide_true]
        rw [Hlast sid rfl]
        wp_auto
        have := Hsoff sid rfl
        wp_if_destruct
        · iapply HΦ
          isplitl
          · close_unstable
          ipureintro
          refine ⟨⟨fun h => (nomatch h), ?_⟩, fun h => (nomatch h)⟩
          rintro (Hc | Hc)
          · simp only [List.length_nil] at Hc; omega
          · exact absurd Hc Hnsnap
        · exfalso; apply Hnsnap; refine ⟨sid, rfl, ?_⟩; word
      | none =>
        simp only [ne_eq, not_true_eq_false, decide_false]
        wp_auto
        iapply HΦ
        isplitl
        · close_unstable
        ipureintro
        refine ⟨⟨fun h => (nomatch h), ?_⟩, fun h => (nomatch h)⟩
        rintro (Hc | Hc)
        · simp only [List.length_nil] at Hc; omega
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
      · have Hbnd : 0 ≤ sint.Z (i - uv.offset') ∧
            sint.Z (i - uv.offset') < sint.Z uv.entries'.len := by
          constructor <;> word
        simp only [Hbnd, and_self, ↓reduceIte]
        have Hk : (sint.Z (i - uv.offset')).toNat = (uint.Z i - uint.Z uv.offset').toNat := by
          word
        have Hlt : (sint.Z (i - uv.offset')).toNat < uents.length := by word
        obtain ⟨e, He_lk⟩ : ∃ e, uents[(sint.Z (i - uv.offset')).toNat]? = some e :=
          ⟨_, List.getElem?_eq_getElem Hlt⟩
        icases Hents with #Hents
        icases ownSlice_elem_acc (sint.Z (i - uv.offset')) e uv.entries' _ uents Hbnd.1 He_lk
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
