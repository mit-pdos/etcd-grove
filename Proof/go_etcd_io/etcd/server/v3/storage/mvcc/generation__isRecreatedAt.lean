/-
Proof of `Spec/.../mvcc/generation__isRecreatedAt.lean` (M2, 2026-10-28). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.generation__isEmpty
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.generation__isRecreatedAt

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.generation.isRecreatedAt.wp_proof
    (wp_isEmpty : mvcc.generation.isEmpty.spec (GF := GF) (hG := hG)) :
    mvcc.generation.isRecreatedAt.spec (GF := GF) (hG := hG) := by
  intro g gv gm dq rev
  wp_start as ⟨%Hg, Hgv, Hgm⟩
  wp_auto
  wp_apply wp_isEmpty.2 g gv gm dq $$ [$Hgv $Hgm] as ⟨Hgv, Hgm⟩
  · ipureintro; exact Hg
  cases hr : gm.revs with
  | nil =>
    simp only [hr, decide_true, Bool.not_true]
    wp_auto
    have hf : mvcc.genRecreatedAt rev gm = false := by unfold mvcc.genRecreatedAt; rw [hr]
    rw [hf]
    iapply HΦ
    iframe
  | cons r rs =>
    simp only [hr, reduceCtorEq, decide_false, Bool.not_false]
    iunfold mvcc.ownGen at Hgm
    icases Hgm with ⟨%Hfields, Hrevs, Hcap⟩
    ihave %Hlen := ownSlice_len _ _ _ $$ Hrevs
    rw [List.length_map, hr] at Hlen
    icases mvcc.gen_split _ _ _ $$ Hgv with ⟨Hver, Hcreated, Hrevsf, %Hnn⟩
    have Hb0 : 0 ≤ sint.Z (W64 0 : w64) ∧ sint.Z (W64 0 : w64) < sint.Z gv.revs'.len := by
      simp at Hlen; unfold sint.nat at Hlen; constructor <;> word
    wp_auto
    simp only [Hb0, _root_.and_self, ↓reduceIte]
    have H0 : (gm.revs.map mvcc.revVal)[(sint.Z (W64 0 : w64)).toNat]? = some (mvcc.revVal r) := by
      rw [hr]; rfl
    icases ownSlice_elem_acc (sint.Z (W64 0 : w64)) _ gv.revs' dq _ Hb0.1 H0 $$ Hrevs
      with ⟨Hel, Hback⟩
    icases mvcc.rev_split _ _ _ $$ Hel with ⟨HMain, HSub, %Hlnn⟩
    wp_auto
    ihave Hel := mvcc.rev_combine _ _ dq Hlnn $$ [HMain HSub]
    · iframe HMain HSub
    ispecialize Hback $$ %_ Hel
    rw [mvcc.set_same H0]
    ihave Hgv := mvcc.gen_combine g gv dq Hg $$ [Hver Hcreated Hrevsf]
    · iframe Hver Hcreated Hrevsf
    have hdec : decide (r.main = rev) = mvcc.genRecreatedAt rev gm := by
      unfold mvcc.genRecreatedAt; rw [hr]
      apply decide_eq_decide.2
      constructor
      · intro h; rw [h]
      · intro h; word
    rw [hdec]
    iapply HΦ
    iframe Hgv
    iunfold mvcc.ownGen
    iframe Hback Hcap
    ipureintro; exact Hfields

end proof

end EtcdGrove
end Perennial
