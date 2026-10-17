/-
Proof of `Spec/.../mvcc/generation__isRecreatedAt.lean` (etcd-io/etcd#22377).
The hypotheses are the callees' specs, in the order of `etc/link-lean-first-mvcc.txt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.generation__isRecreatedAt
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.generation__isEmpty

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

theorem mvcc.generation.isRecreatedAt.wp_proof
    (hE : mvcc.generation.isEmpty.spec (GF := GF) (hG := hG)) :
    mvcc.generation.isRecreatedAt.spec (GF := GF) (hG := hG) := by
  intro g gv gm dq rev
  wp_start as ⟨%Hg, Hgv, Hgm⟩
  wp_auto
  wp_apply (hE.2 g gv gm dq) $$ [Hgv Hgm] as ⟨Hgv, Hgm⟩
  · iframe; ipureintro; exact Hg
  wp_if_destruct
  · -- empty: not re-created
    have hne : gm.revs = [] := by simpa using Hif
    rw [show decide (mvcc.RecreatedAt rev gm) = false by
      simp [mvcc.RecreatedAt, hne]]
    iapply HΦ
    iframe
  · -- its first revision
    have hne : gm.revs ≠ [] := by simpa using Hif
    iunfold mvcc.ownGen at Hgm
    icases Hgm with ⟨%Hfields, Hrevs, Hcap⟩
    ihave %Hrlen := ownSlice_len _ _ _ $$ Hrevs
    rw [List.length_map] at Hrlen
    icases mvcc.gen_split _ _ _ $$ Hgv with ⟨Hver, Hcreated, Hrevsf, %Hnn⟩
    have hpos := List.length_pos_iff.2 hne
    have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z gv.revs'.len := by
      have := Hrlen.1; word
    have H0 : (gm.revs.map mvcc.revVal)[(sint.Z (W64 0)).toNat]? =
        some (mvcc.revVal (gm.revs.headD mvcc.Rev.zero)) := by
      rw [show (sint.Z (W64 0)).toNat = 0 by rfl, List.getElem?_map]
      cases h : gm.revs with
      | nil => exact absurd h hne
      | cons a t => rfl
    wp_auto
    simp only [Hb0, _root_.and_self, ↓reduceIte]
    icases ownSlice_elem_acc (sint.Z (W64 0)) _ gv.revs' dq _ Hb0.1 H0 $$ Hrevs with ⟨Hel, Hback⟩
    icases mvcc.rev_split _ _ _ $$ Hel with ⟨HMain, HSub, %Hlnn⟩
    wp_auto
    ihave Hel := mvcc.rev_combine (sliceIndexRef Revision (sint.Z (W64 0)) gv.revs')
      _ dq Hlnn $$ [HMain HSub]
    · iframe HMain HSub
    ispecialize Hback $$ %_ Hel
    rw [mvcc.set_same H0]
    have hdec : decide ((gm.revs.headD mvcc.Rev.zero).main = rev) = decide (mvcc.RecreatedAt rev gm) := by
      apply decide_eq_decide.2
      unfold mvcc.RecreatedAt mvcc.headZ
      constructor
      · intro h; exact ⟨hne, by rw [h]⟩
      · rintro ⟨-, h⟩; word
    rw [hdec]
    iapply HΦ
    isplitl [Hver Hcreated Hrevsf]
    · iapply mvcc.gen_combine _ _ _ Hnn; iframe Hver Hcreated Hrevsf
    iunfold mvcc.ownGen
    iframe Hback Hcap
    ipureintro; exact Hfields

end proof

end EtcdGrove
end Perennial
