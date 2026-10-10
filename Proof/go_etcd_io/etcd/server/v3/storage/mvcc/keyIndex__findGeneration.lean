/-
Proof of `Spec/.../mvcc/keyIndex__findGeneration.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__findGeneration

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

theorem mvcc.keyIndex.findGeneration.wp_proof :
    mvcc.keyIndex.findGeneration.spec (GF := GF) (hG := hG) := by
  intro p gs ki dq rev
  wp_start as Hki
  iunfold mvcc.ownKi at Hki
  icases Hki with ⟨Hmod, Hgs, Hgens⟩
  ihave %Hlen := mvcc.ownGens_len _ _ _ $$ Hgens
  wp_auto
  -- the scan from `cg` down: what is left to look at is `kiFindGenAux` with `cg + 1` generations
  ihave IH : iprop(∃ cg : w64,
      "cg" ∷ cg_ptr ↦ cg ∗
      "%Hcg" ∷ ⌜-1 ≤ sint.Z cg ∧ sint.Z cg ≤ (ki.gens.length : Int) - 1 ∧
        mvcc.kiFindGen ki rev = mvcc.kiFindGenAux ki.gens rev (sint.Z cg + 1).toNat⌝) $$ [cg]
  · iexists (gs.len - W64 1)
    iframe cg
    ipureintro
    refine ⟨by word, by word, ?_⟩
    unfold mvcc.kiFindGen
    congr 1
    word
  wp_for IH
  wp_if_destruct
  · -- `cg >= 0`: look at generation `cg`
    have Hcgn : (sint.Z cg).toNat < ki.gens.length := by word
    have Hb : 0 ≤ sint.Z cg ∧ sint.Z cg < sint.Z gs.len := by word
    simp only [Hb, and_self, ↓reduceIte]
    obtain ⟨gm, Hgm⟩ : ∃ gm, ki.gens[(sint.Z cg).toNat]? = some gm :=
      ⟨_, List.getElem?_eq_getElem Hcgn⟩
    icases mvcc.ownGens_acc_z gs ki.gens dq (sint.Z cg) gm Hb.1 Hgm $$ Hgens
      with ⟨%gv, Hel, Hg, Hback⟩
    iunfold mvcc.ownGen at Hg
    icases Hg with ⟨%Hfields, Hrevs, Hcap⟩
    ihave %Hrlen := ownSlice_len _ _ _ $$ Hrevs
    rw [List.length_map] at Hrlen
    icases mvcc.gen_split _ _ _ $$ Hel with ⟨Hver, Hcreated, Hrevsf, %Hnn⟩
    wp_auto
    have Hgd : ki.gens.getD (sint.Z cg).toNat mvcc.Gen.empty = gm := by
      simp [List.getD_eq_getElem?_getD, Hgm]
    have Hsucc : (sint.Z cg + 1).toNat = (sint.Z cg).toNat + 1 := by omega
    have Hcg1 : sint.Z (cg - W64 1) = sint.Z cg - 1 := by word
    wp_if_destruct
    · -- the generation is empty: skip it
      have hrevs : gm.revs = [] := by
        apply List.eq_nil_of_length_eq_zero; rw [Hrlen.1, Hif]; rfl
      ihave Hel := mvcc.gen_combine (sliceIndexRef generation (sint.Z cg) gs) gv dq Hnn
        $$ [Hver Hcreated Hrevsf]
      · iframe Hver Hcreated Hrevsf
      ihave Hg : iprop(mvcc.ownGen gv gm dq) $$ [Hrevs Hcap]
      · iunfold mvcc.ownGen; iframe Hrevs Hcap; ipureintro; exact Hfields
      ispecialize Hback $$ %gv %gm Hel Hg
      rw [mvcc.set_same Hgm]
      wp_for_post
      iframe
      iexists cg - W64 1
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [Hcg.2.2, Hsucc, mvcc.kiFindGenAux_skip (by rw [Hgd]; exact hrevs)]
      congr 1; rw [Hcg1]; omega
    · -- the generation is not empty: `g` is a copy of it
      have hne : gm.revs ≠ [] := by
        intro h; apply Hif; rw [h] at Hrlen; simp only [List.length_nil] at Hrlen; word
      ihave Hel := mvcc.gen_combine (sliceIndexRef generation (sint.Z cg) gs) gv dq Hnn
        $$ [Hver Hcreated Hrevsf]
      · iframe Hver Hcreated Hrevsf
      simp only [Hb, _root_.and_self, ↓reduceIte]
      wp_auto
      -- the generation's first and last revisions
      have Hfirst := mvcc.revs_first gm.revs hne
      have Hlast := mvcc.revs_last gm.revs gv.revs'.len hne Hrlen.1
      have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z gv.revs'.len := by
        have := List.length_pos_iff.2 hne; word
      have HbL : 0 ≤ sint.Z (gv.revs'.len - W64 1) ∧
          sint.Z (gv.revs'.len - W64 1) < sint.Z gv.revs'.len := by
        have := List.length_pos_iff.2 hne; word
      wp_if_destruct
      · -- the last generation (`cg` is `lastg`): no tombstone to look at
        have HNOT : ¬ ((sint.Z (gs.len - W64 1)).toNat ≠ ki.gens.length - 1 ∧
            sint.Z ((ki.gens.getD (sint.Z (gs.len - W64 1)).toNat mvcc.Gen.empty).revs.getLastD
              mvcc.Rev.zero).main ≤ sint.Z rev) := by
          intro h; apply h.1; rw [Hlen.1]; word

        -- the generation's first revision: is the key alive at `rev` in it?
        simp only [Hb0, _root_.and_self, ↓reduceIte]
        icases ownSlice_elem_acc (sint.Z (W64 0)) _ gv.revs' dq _ Hb0.1 Hfirst $$ Hrevs
          with ⟨Hfel, Hfback⟩
        icases mvcc.rev_split _ _ _ $$ Hfel with ⟨HfMain, HfSub, %Hfnn⟩
        wp_auto
        ihave Hfel := mvcc.rev_combine (sliceIndexRef Revision (sint.Z (W64 0)) gv.revs') _ dq Hfnn
          $$ [HfMain HfSub]
        · iframe HfMain HfSub
        ispecialize Hfback $$ %_ Hfel
        rw [mvcc.set_same Hfirst]
        irename Hfback => Hrevs
        (try simp only [mvcc.revVal_main])
        wp_if_destruct
        · -- found: the generation at `cg`
          simp only [Hb, _root_.and_self, ↓reduceIte]
          wp_auto
          ihave Hg : iprop(mvcc.ownGen gv gm dq) $$ [Hrevs Hcap]
          · iunfold mvcc.ownGen; iframe Hrevs Hcap; ipureintro; exact Hfields
          ispecialize Hback $$ %gv %gm Hel Hg
          rw [mvcc.set_same Hgm]
          have Hfound : mvcc.kiFindGen ki rev = some (sint.Z (gs.len - W64 1)).toNat := by
            rw [Hcg.2.2, Hsucc]
            apply mvcc.kiFindGenAux_found (by rw [Hgd]; exact hne) HNOT
            rw [Hgd]; exact Hif
          wp_for_post
          rw [Hfound]
          simp only [mvcc.genPtr]
          rw [show (((sint.Z (gs.len - W64 1)).toNat : Nat) : Int) = sint.Z (gs.len - W64 1) by omega]
          iapply HΦ
          iunfold mvcc.ownKi
          iframe Hmod Hgs Hback
        · -- not yet created at `rev`: the previous generation
          ihave Hg : iprop(mvcc.ownGen gv gm dq) $$ [Hrevs Hcap]
          · iunfold mvcc.ownGen; iframe Hrevs Hcap; ipureintro; exact Hfields
          ispecialize Hback $$ %gv %gm Hel Hg
          rw [mvcc.set_same Hgm]
          wp_for_post
          iframe
          iexists (gs.len - W64 1) - W64 1
          iframe
          ipureintro
          refine ⟨by word, by word, ?_⟩
          rw [Hcg.2.2, Hsucc, mvcc.kiFindGenAux_next (by rw [Hgd]; exact hne) HNOT
            (by rw [Hgd]; exact Hif)]
          congr 1; rw [Hcg1]; omega
      · -- not the last generation: its tombstone
        have Hcgne : (sint.Z cg).toNat ≠ ki.gens.length - 1 := by
          intro h; apply Hif; rw [Hlen.1] at h; word
        simp only [HbL, _root_.and_self, ↓reduceIte]
        icases ownSlice_elem_acc (sint.Z (gv.revs'.len - W64 1)) _ gv.revs' dq _ HbL.1 Hlast $$ Hrevs
          with ⟨Hlel, Hlback⟩
        icases mvcc.rev_split _ _ _ $$ Hlel with ⟨HlMain, HlSub, %Hlnn⟩
        wp_auto
        ihave Hlel := mvcc.rev_combine (sliceIndexRef Revision (sint.Z (gv.revs'.len - W64 1)) gv.revs')
          _ dq Hlnn $$ [HlMain HlSub]
        · iframe HlMain HlSub
        ispecialize Hlback $$ %_ Hlel
        rw [mvcc.set_same Hlast]
        irename Hlback => Hrevs
        (try simp only [mvcc.revVal_main])
        wp_if_destruct
        · -- deleted at or before `rev`: the key is absent
          ihave Hg : iprop(mvcc.ownGen gv gm dq) $$ [Hrevs Hcap]
          · iunfold mvcc.ownGen; iframe Hrevs Hcap; ipureintro; exact Hfields
          ispecialize Hback $$ %gv %gm Hel Hg
          rw [mvcc.set_same Hgm]
          have Hnone : mvcc.kiFindGen ki rev = none := by
            rw [Hcg.2.2, Hsucc]
            apply mvcc.kiFindGenAux_tomb (by rw [Hgd]; exact hne) Hcgne
            rw [Hgd]; exact Hif
          wp_for_post
          rw [Hnone]
          simp only [mvcc.genPtr]
          iapply HΦ
          iunfold mvcc.ownKi
          iframe Hmod Hgs Hback
        · have HNOT : ¬ ((sint.Z cg).toNat ≠ ki.gens.length - 1 ∧
              sint.Z ((ki.gens.getD (sint.Z cg).toNat mvcc.Gen.empty).revs.getLastD
                mvcc.Rev.zero).main ≤ sint.Z rev) := by
            intro h; apply Hif; rw [← Hgd]; exact h.2

          -- the generation's first revision: is the key alive at `rev` in it?
          simp only [Hb0, _root_.and_self, ↓reduceIte]
          icases ownSlice_elem_acc (sint.Z (W64 0)) _ gv.revs' dq _ Hb0.1 Hfirst $$ Hrevs
            with ⟨Hfel, Hfback⟩
          icases mvcc.rev_split _ _ _ $$ Hfel with ⟨HfMain, HfSub, %Hfnn⟩
          wp_auto
          ihave Hfel := mvcc.rev_combine (sliceIndexRef Revision (sint.Z (W64 0)) gv.revs') _ dq Hfnn
            $$ [HfMain HfSub]
          · iframe HfMain HfSub
          ispecialize Hfback $$ %_ Hfel
          rw [mvcc.set_same Hfirst]
          irename Hfback => Hrevs
          (try simp only [mvcc.revVal_main])
          wp_if_destruct
          · -- found: the generation at `cg`
            simp only [Hb, _root_.and_self, ↓reduceIte]
            wp_auto
            ihave Hg : iprop(mvcc.ownGen gv gm dq) $$ [Hrevs Hcap]
            · iunfold mvcc.ownGen; iframe Hrevs Hcap; ipureintro; exact Hfields
            ispecialize Hback $$ %gv %gm Hel Hg
            rw [mvcc.set_same Hgm]
            have Hfound : mvcc.kiFindGen ki rev = some (sint.Z cg).toNat := by
              rw [Hcg.2.2, Hsucc]
              apply mvcc.kiFindGenAux_found (by rw [Hgd]; exact hne) HNOT
              rw [Hgd]; exact Hif
            wp_for_post
            rw [Hfound]
            simp only [mvcc.genPtr]
            rw [show (((sint.Z cg).toNat : Nat) : Int) = sint.Z cg by omega]
            iapply HΦ
            iunfold mvcc.ownKi
            iframe Hmod Hgs Hback
          · -- not yet created at `rev`: the previous generation
            ihave Hg : iprop(mvcc.ownGen gv gm dq) $$ [Hrevs Hcap]
            · iunfold mvcc.ownGen; iframe Hrevs Hcap; ipureintro; exact Hfields
            ispecialize Hback $$ %gv %gm Hel Hg
            rw [mvcc.set_same Hgm]
            wp_for_post
            iframe
            iexists cg - W64 1
            iframe
            ipureintro
            refine ⟨by word, by word, ?_⟩
            rw [Hcg.2.2, Hsucc, mvcc.kiFindGenAux_next (by rw [Hgd]; exact hne) HNOT
              (by rw [Hgd]; exact Hif)]
            congr 1; rw [Hcg1]; omega
  · -- `cg < 0`: no generation
    have Hm1 : sint.Z cg = -1 := by word
    have Hnone : mvcc.kiFindGen ki rev = none := by
      rw [Hcg.2.2, show (sint.Z cg + 1).toNat = 0 by omega]; rfl
    rw [Hnone]
    simp only [mvcc.genPtr]
    iapply HΦ
    iunfold mvcc.ownKi
    iframe Hmod Hgs Hgens

end proof

end EtcdGrove
end Perennial
