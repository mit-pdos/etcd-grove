/-
Proof of `Spec/.../mvcc/generation__walk.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.generation__walk

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.generation.walk.wp_proof : mvcc.generation.walk.spec (GF := GF) (hG := hG) := by
  intro g gv gm dq f p
  wp_start as ⟨Hgv, Hgm, #Hf⟩
  iunfold mvcc.ownGen at Hgm
  icases Hgm with ⟨%Hfields, Hrevs, Hcap⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hrevs
  rw [List.length_map] at Hlen
  icases mvcc.gen_split _ _ _ $$ Hgv with ⟨Hver, Hcreated, Hrevsf, %Hg⟩
  wp_auto
  -- `slice.forRange` has its own counter (`i_ptr`); the Go `i` (`igo`) is assigned `$key`
  rename_i igo
  irename : (igo ↦ zero_val w64 : IProp GF) => Higo
  ihave IH : iprop(∃ (n k : w64),
      "i" ∷ i_ptr ↦ n ∗
      "Higo" ∷ igo ↦ k ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ gm.revs.length ∧
        ∀ (j : Nat) (hj : j < gm.revs.length), gm.revs.length - sint.nat n ≤ j →
          p (gm.revs[j]'hj) = true⌝) $$ [i Higo]
  · iexists W64 0, _
    iframe i Higo
    ipureintro
    refine ⟨by word, by word, ?_⟩
    intro j hj h
    rw [show sint.nat (W64 0) = 0 by rfl] at h
    omega
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < gm.revs.length := by word
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z gv.revs'.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd, and_self, ↓reduceIte]
    -- the range value (unused): the element at `n`
    obtain ⟨e, He⟩ : ∃ e, gm.revs[sint.nat n]? = some e := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have He' : (List.map mvcc.revVal gm.revs)[(sint.Z n).toNat]? = some (mvcc.revVal e) := by
      rw [List.getElem?_map]; show (gm.revs[sint.nat n]?).map _ = _; rw [He]; rfl
    wp_apply wp_load_slice_index gv.revs' (sint.Z n) _ dq (mvcc.revVal e) Hn.1 $$ [Hrevs] as Hrevs
    · iframe; ipureintro; exact He'
    -- `g.revs[l-i-1]`: the element at `len - n - 1`
    have Hj : sint.Z (gv.revs'.len - n - W64 1) = (gm.revs.length - sint.nat n - 1 : Nat) := by word
    have Hbnd2 : 0 ≤ sint.Z (gv.revs'.len - n - W64 1) ∧
        sint.Z (gv.revs'.len - n - W64 1) < sint.Z gv.revs'.len := by word
    simp only [Hbnd2, and_self, ↓reduceIte]
    have Hjlt : gm.revs.length - sint.nat n - 1 < gm.revs.length := by omega
    obtain ⟨e1, He1⟩ : ∃ e1, gm.revs[gm.revs.length - sint.nat n - 1]? = some e1 :=
      ⟨_, List.getElem?_eq_getElem Hjlt⟩
    have He1' : (List.map mvcc.revVal gm.revs)[(sint.Z (gv.revs'.len - n - W64 1)).toNat]? =
        some (mvcc.revVal e1) := by
      rw [Hj, List.getElem?_map]; show (gm.revs[gm.revs.length - sint.nat n - 1]?).map _ = _
      rw [He1]; rfl
    wp_apply wp_load_slice_index gv.revs' (sint.Z (gv.revs'.len - n - W64 1)) _ dq
      (mvcc.revVal e1) Hbnd2.1 $$ [Hrevs] as Hrevs
    · iframe; ipureintro; exact He1'
    iunfold mvcc.walkFnSpec at Hf
    wp_apply Hf $$ %(mvcc.revVal e1)
    simp only [mvcc.revOf_revVal]
    cases hp : p e1
    · -- `f` returned false: this is the position
      wp_auto
      have Hw : mvcc.genWalk gm.revs p = ((gm.revs.length - sint.nat n - 1 : Nat) : Int) := by
        apply mvcc.genWalk_eq_some _ Hjlt
        · rw [(List.getElem?_eq_some_iff.1 He1).2]; exact hp
        · intro k hk hgt
          exact Hn.2.2 k hk (by omega)
      wp_for_post
      rw [show W64 (mvcc.genWalk gm.revs p) = gv.revs'.len - n - W64 1 by rw [Hw]; word]
      iapply HΦ
      isplitl [Hver Hcreated Hrevsf]
      · iapply mvcc.gen_combine _ _ _ Hg; iframe Hver Hcreated Hrevsf
      iunfold mvcc.ownGen
      iframe Hrevs Hcap
      ipureintro; exact Hfields
    · -- `f` returned true: on to the next
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, n
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      intro j hj hle
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word] at hle
      by_cases hjn : j = gm.revs.length - sint.nat n - 1
      · subst hjn
        rw [(List.getElem?_eq_some_iff.1 He1).2]; exact hp
      · exact Hn.2.2 j hj (by omega)
  · -- the loop is done: every revision passed
    have Hall : ∀ r ∈ gm.revs, p r = true := by
      intro r hr
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hr
      exact Hn.2.2 j hj (by word)
    rw [mvcc.genWalk_eq_none Hall]
    iapply HΦ
    isplitl [Hver Hcreated Hrevsf]
    · iapply mvcc.gen_combine _ _ _ Hg; iframe Hver Hcreated Hrevsf
    iunfold mvcc.ownGen
    iframe Hrevs Hcap
    ipureintro; exact Hfields

end proof

end EtcdGrove
end Perennial
