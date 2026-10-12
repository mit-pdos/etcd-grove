/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.checkRangeRequest

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api
  go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.checkRangeRequest.wp_proof :
    v3rpc.checkRangeRequest.spec (GF := GF) (hG := hG) := by
  intro r o
  wp_start as #Hr
  ihave Hinit : (go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.v3rpcInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, ⟨#HeK, #HeS, -, -, -, -, -⟩, Hmaps, -⟩
  iunfold go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.sortNameMaps at Hmaps
  icases Hmaps with ⟨⟨%mo, %Mo, #Hmo, #Hmos, %HMo⟩, ⟨%mt, %Mt, #Hmt, #Hmts, %HMt⟩⟩
  iunfold go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.errVarSet at HeK HeS
  icases HeK with ⟨%eK, #HeK⟩
  icases HeS with ⟨%eS, #HeS⟩
  iunfold txn.rangeRequestIs at Hr
  icases Hr with ⟨%Hrn, %ksl, %esl, %k, %e, %rev, %limit, %order, %target, %ser, %ko, %co,
    %minM, %maxM, %minC, %maxC, #Hk, #Hks, -, -, -, -, #Ho, #Ht, -, -, -, -, -, -, -, %Hop⟩
  ihave %Hkl := ownSlice_len _ _ _ $$ Hks
  subst Hop
  wp_auto
  wp_if_destruct
  · iapply HΦ
    have hk : k = [] := by
      apply List.eq_nil_of_length_eq_zero; word
    simp only [v3rpc.rangeCheck, txn.rangeOpOf, hk, ↓reduceIte]
    unfold v3rpc.checkRes txn.errVarIs v3rpc.CheckErr.var
    iexists eK; iframe HeK; itrivial
  have hk : k ≠ [] := by
    intro h; subst h; simp at Hkl; word
  have hz : ∀ x : w32, sint.Z (W64 (sint.Z x) : w64) = sint.Z x := by
    intro x; word
  wp_apply (wp_map_lookup2 _ _ mo Mo order DFrac.discard) $$ [$Hmos]
  iintro -
  wp_auto
  wp_if_destruct
  rotate_left
  · iapply HΦ
    have ho : ¬ (0 ≤ sint.Z order ∧ sint.Z order ≤ 2) := fun h => Hif ((HMo order).2 h)
    simp only [v3rpc.rangeCheck, v3rpc.sortOrderKnown, txn.rangeOpOf, hk, hz, ho, ↓reduceIte, _root_.and_self, _root_.and_true, _root_.true_and, ite_self,
      decide_false, Bool.not_false]
    unfold v3rpc.checkRes txn.errVarIs v3rpc.CheckErr.var
    iexists eS; iframe HeS; itrivial
  have ho : 0 ≤ sint.Z order ∧ sint.Z order ≤ 2 := (HMo order).1 Hif
  wp_apply (wp_map_lookup2 _ _ mt Mt target DFrac.discard) $$ [$Hmts]
  iintro -
  wp_auto
  wp_if_destruct
  rotate_left
  · iapply HΦ
    have ht : ¬ (0 ≤ sint.Z target ∧ sint.Z target ≤ 4) := fun h => Hif ((HMt target).2 h)
    simp only [v3rpc.rangeCheck, v3rpc.sortOrderKnown, v3rpc.sortTargetKnown, txn.rangeOpOf, hk,
      hz, ho, ht, ↓reduceIte, _root_.and_self, _root_.and_true, _root_.true_and, ite_self, decide_false, _root_.decide_true, Bool.not_false, Bool.not_true,
      Bool.false_eq_true]
    unfold v3rpc.checkRes txn.errVarIs v3rpc.CheckErr.var
    iexists eS; iframe HeS; itrivial
  have ht : 0 ≤ sint.Z target ∧ sint.Z target ≤ 4 := (HMt target).1 Hif
  iapply HΦ
  simp only [v3rpc.rangeCheck, v3rpc.sortOrderKnown, v3rpc.sortTargetKnown, txn.rangeOpOf, hk,
    hz, ho, ht, ↓reduceIte, _root_.and_self, _root_.and_true, _root_.true_and, ite_self, _root_.decide_true, Bool.not_true, Bool.false_eq_true]
  unfold v3rpc.checkRes
  itrivial

end proof

end EtcdGrove
end Perennial
