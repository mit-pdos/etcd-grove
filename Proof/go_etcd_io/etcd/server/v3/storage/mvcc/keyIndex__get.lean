/-
Proof of `Spec/.../mvcc/keyIndex__get.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__get
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__isEmpty
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__findGeneration
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.generation__isEmpty
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

theorem mvcc.keyIndex.get.wp_proof
    (hIE : mvcc.keyIndex.isEmpty.spec (GF := GF) (hG := hG))
    (hFG : mvcc.keyIndex.findGeneration.spec (GF := GF) (hG := hG))
    (hGE : mvcc.generation.isEmpty.spec (GF := GF) (hG := hG))
    (hW : mvcc.generation.walk.spec (GF := GF) (hG := hG)) :
    mvcc.keyIndex.get.spec (GF := GF) (hG := hG) := by
  intro p gs ki dq lg atRev e
  wp_start as ⟨%Hne, Hki, #Herr⟩
  wp_auto
  wp_apply (hIE p gs ki dq) $$ [Hki] as Hki
  · iframe Hki
  rw [Hne]
  wp_auto
  wp_apply (hFG p gs ki dq atRev) $$ [Hki] as Hki
  · iframe Hki
  cases hfg : mvcc.kiFindGen ki atRev with
  | none =>
    -- no generation: the key is absent
    simp only [mvcc.genPtr]
    wp_apply (hGE.1 null rfl)
    rw [show mvcc.kiGetVal ki atRev (GoInterface.ok e) =
      PairV (PairV (PairV #(zero_val Revision) #(zero_val Revision)) #(W64 0)) #(GoInterface.ok e)
      by simp [mvcc.kiGetVal, mvcc.kiGet, hfg]]
    wp_end
  | some gi =>
    simp only [mvcc.genPtr]
    have Hgi := mvcc.kiFindGen_lt hfg
    obtain ⟨gm, Hgm⟩ : ∃ gm, ki.gens[gi]? = some gm := ⟨_, List.getElem?_eq_getElem Hgi⟩
    have Hgd : ki.gens.getD gi mvcc.Gen.empty = gm := by simp [List.getD_eq_getElem?_getD, Hgm]
    iunfold mvcc.ownKi at Hki
    icases Hki with ⟨Hmod, Hgs, Hgens⟩
    icases mvcc.ownGens_acc gs ki.gens dq gi gm Hgm $$ Hgens with ⟨%gv, Hel, Hg, Hback⟩
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hel
    wp_apply (hGE.2 _ gv gm dq) $$ [Hel Hg] as ⟨Hel, Hg⟩
    · iframe; ipureintro; exact Hnn
    wp_if_destruct
    · -- an empty generation: the key is absent
      ispecialize Hback $$ %gv %gm Hel Hg
      rw [mvcc.set_same Hgm]
      rw [show mvcc.kiGetVal ki atRev (GoInterface.ok e) =
        PairV (PairV (PairV #(zero_val Revision) #(zero_val Revision)) #(W64 0)) #(GoInterface.ok e)
        by simp only [mvcc.kiGetVal, mvcc.kiGet, hfg, Hgd, Hif, ↓reduceIte]]
      iapply HΦ
      iunfold mvcc.ownKi
      iframe Hmod Hgs Hback
    · -- walk the generation for the last revision at or before `atRev`
      ipersist atRev
      have hne : gm.revs ≠ [] := Hif
      wp_apply (hW (sliceIndexRef generation (gi : Int) gs) gv gm dq _
        (mvcc.pAbove atRev)) $$ [Hel Hg] as ⟨Hel, Hg⟩
      · iframe Hel Hg
        iunfold mvcc.walkFnSpec
        imodintro
        iintro %r
        wp_start
        wp_auto
        simp only [mvcc.pAbove, mvcc.revOf_main]
        by_cases h : sint.Z atRev < sint.Z r.Main'
        · simp only [h, decide_true]; wp_end
        · simp only [h, decide_false]; wp_end
      obtain ⟨n, hn⟩ : ∃ n, n = mvcc.genWalk gm.revs (mvcc.pAbove atRev) :=
        ⟨_, rfl⟩
      have Hrange := mvcc.genWalk_range gm.revs (mvcc.pAbove atRev)
      rw [← hn] at Hrange
      rw [← hn]
      iunfold mvcc.ownGen at Hg
      icases Hg with ⟨%Hfields, Hrevs, Hcap⟩
      ihave %Hrlen := ownSlice_len _ _ _ $$ Hrevs
      rw [List.length_map] at Hrlen
      wp_if_destruct
      · -- every revision is above `atRev`: the key is absent
        have Hw : mvcc.genWalk gm.revs (mvcc.pAbove atRev) = -1 := by
          rw [← hn]; have := Hif; word
        ihave Hg : iprop(mvcc.ownGen gv gm dq) $$ [Hrevs Hcap]
        · iunfold mvcc.ownGen; iframe Hrevs Hcap; ipureintro; exact Hfields
        ispecialize Hback $$ %gv %gm Hel Hg
        rw [mvcc.set_same Hgm]
        rw [show mvcc.kiGetVal ki atRev (GoInterface.ok e) =
          PairV (PairV (PairV #(zero_val Revision) #(zero_val Revision)) #(W64 0)) #(GoInterface.ok e)
          by simp only [mvcc.kiGetVal, mvcc.kiGet, hfg, Hgd, hne, Hw, ↓reduceIte]]
        iapply HΦ
        iunfold mvcc.ownKi
        iframe Hmod Hgs Hback
      · -- the revision at `n`
        have Hw0 : 0 ≤ n := by
          have hne1 : n ≠ -1 := fun h => Hif (by rw [h])
          omega
        have Hnlt : n.toNat < gm.revs.length := by omega
        have Hbn : 0 ≤ sint.Z (W64 n) ∧ sint.Z (W64 n) < sint.Z gv.revs'.len := by word
        icases mvcc.gen_split _ _ _ $$ Hel with ⟨Hver, Hcreated, Hrevsf, -⟩
        wp_auto
        simp only [Hbn, _root_.and_self, ↓reduceIte]
        have Hel' : (List.map mvcc.revVal gm.revs)[(sint.Z (W64 n)).toNat]? =
            some (mvcc.revVal (gm.revs.getD n.toNat mvcc.Rev.zero)) := by
          rw [List.getElem?_map, show (sint.Z (W64 n)).toNat = n.toNat by word,
            List.getD_eq_getElem?_getD]
          obtain ⟨r, hr⟩ : ∃ r, gm.revs[n.toNat]? = some r := ⟨_, List.getElem?_eq_getElem Hnlt⟩
          rw [hr]; rfl
        wp_apply wp_load_slice_index gv.revs' (sint.Z (W64 n)) _ dq _ Hbn.1 $$ [Hrevs] as Hrevs
        · iframe; ipureintro; exact Hel'
        ihave Hel := mvcc.gen_combine (sliceIndexRef generation (gi : Int) gs) gv dq Hnn
          $$ [Hver Hcreated Hrevsf]
        · iframe Hver Hcreated Hrevsf
        ihave Hg : iprop(mvcc.ownGen gv gm dq) $$ [Hrevs Hcap]
        · iunfold mvcc.ownGen; iframe Hrevs Hcap; ipureintro; exact Hfields
        ispecialize Hback $$ %gv %gm Hel Hg
        rw [mvcc.set_same Hgm]
        have hne1 : n ≠ -1 := fun h => Hif (by rw [h])
        rw [show mvcc.kiGetVal ki atRev (GoInterface.ok e) =
          PairV (PairV (PairV #(mvcc.revVal (gm.revs.getD n.toNat mvcc.Rev.zero))
            #(mvcc.revVal gm.created))
            #(gm.ver - W64 ((gm.revs.length : Int) - (n.toNat : Int) - 1))) #(GoInterface.nil)
          by simp only [mvcc.kiGetVal, mvcc.kiGet, hfg, Hgd, hne, ↓reduceIte, ← hn, hne1]]
        rw [show gm.ver - W64 ((gm.revs.length : Int) - (n.toNat : Int) - 1) =
          gv.ver' - (gv.revs'.len - W64 n - W64 1) by rw [Hfields.1]; word, ← Hfields.2]
        iapply HΦ
        iunfold mvcc.ownKi
        iframe Hmod Hgs Hback

end proof

end EtcdGrove
end Perennial
