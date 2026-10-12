/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.checkDeleteRequest

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

theorem v3rpc.checkDeleteRequest.wp_proof :
    v3rpc.checkDeleteRequest.spec (GF := GF) (hG := hG) := by
  intro r o
  wp_start as #Hr
  ihave Hinit : (go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.v3rpcInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, ⟨#HeK, -, -, -, -, -, -⟩, -, -⟩
  iunfold txn.deleteRangeRequestIs at Hr
  icases Hr with ⟨%Hrn, %ksl, %esl, %k, %e, %pk, #Hk, #Hks, -, -, -, %Ho⟩
  ihave %Hkl := ownSlice_len _ _ _ $$ Hks
  subst Ho
  wp_auto
  wp_if_destruct
  · iunfold go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.errVarSet at HeK
    icases HeK with ⟨%ee, #HeK⟩
    wp_auto
    iapply HΦ
    have hk : k = [] := by
      apply List.eq_nil_of_length_eq_zero; word
    simp only [v3rpc.deleteCheck, txn.deleteOpOf, hk, ↓reduceIte]
    unfold v3rpc.checkRes txn.errVarIs v3rpc.CheckErr.var
    iexists ee; iframe HeK; itrivial
  · iapply HΦ
    have hk : k ≠ [] := by
      intro h; subst h; simp at Hkl; word
    simp only [v3rpc.deleteCheck, txn.deleteOpOf, hk, ↓reduceIte]
    unfold v3rpc.checkRes
    itrivial

end proof

end EtcdGrove
end Perennial
