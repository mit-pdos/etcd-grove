/-
Proof of `Spec/.../mvcc/keyIndex__isEmpty.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__isEmpty
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

theorem mvcc.keyIndex.isEmpty.wp_proof
    (hE : mvcc.generation.isEmpty.spec (GF := GF) (hG := hG)) :
    mvcc.keyIndex.isEmpty.spec (GF := GF) (hG := hG) := by
  intro p gs ki dq
  wp_start as Hki
  iunfold mvcc.ownKi at Hki
  icases Hki with ⟨Hmod, Hgs, Hgens⟩
  ihave %Hlen := mvcc.ownGens_len _ _ _ $$ Hgens
  wp_auto
  wp_if_destruct
  · -- one generation: is it empty?
    have h1 : ki.gens.length = 1 := by rw [Hlen.1, Hif]; rfl
    obtain ⟨gm0, hgm0⟩ := List.length_eq_one_iff.1 h1
    have Hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z gs.len := by word
    simp only [Hb, and_self, ↓reduceIte]
    rw [show sint.Z (W64 0) = ((0 : Nat) : Int) from rfl]
    icases mvcc.ownGens_acc gs ki.gens dq 0 gm0 (by simp [hgm0]) $$ Hgens
      with ⟨%gv0, Hel, Hg0, Hback⟩
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hel
    wp_apply (hE.2 _ gv0 gm0 dq) $$ [Hel Hg0] as ⟨Hel, Hg0⟩
    · iframe; ipureintro; exact Hnn
    ispecialize Hback $$ %gv0 %gm0 Hel Hg0
    rw [show mvcc.kiIsEmpty ki = decide (gm0.revs = []) by simp [mvcc.kiIsEmpty, hgm0],
      show ki.gens.set 0 gm0 = ki.gens by rw [hgm0]; rfl]
    iapply HΦ
    iunfold mvcc.ownKi
    iframe Hmod Hgs Hback
  · -- not one generation: not empty
    have hne : ki.gens.length ≠ 1 := by
      intro h; apply Hif; rw [Hlen.1] at h; word
    rw [show mvcc.kiIsEmpty ki = false by
      unfold mvcc.kiIsEmpty
      split
      · rename_i g hg; exact absurd (by rw [hg]; rfl) hne
      · rfl]
    iapply HΦ
    iunfold mvcc.ownKi
    iframe Hmod Hgs Hgens

end proof

end EtcdGrove
end Perennial
