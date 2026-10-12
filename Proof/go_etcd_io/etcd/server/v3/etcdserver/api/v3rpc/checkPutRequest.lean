/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.checkPutRequest

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

/-- The end of a branch of `checkPutRequest`: its result against `putCheck`. -/
local macro "v3rpc_put_fin" : tactic => `(tactic| (
  simp only [v3rpc.putCheck, txn.putOpOf, ↓reduceIte, ne_eq, _root_.decide_true,
    decide_false, Bool.false_eq_true, _root_.false_and, _root_.true_and, _root_.and_true,
    _root_.and_self, not_false_eq_true, not_true_eq_false, *]
  unfold v3rpc.checkRes
  first
    | itrivial
    | (unfold txn.errVarIs v3rpc.CheckErr.var; iexists _; iframe #; itrivial)))

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.checkPutRequest.wp_proof :
    v3rpc.checkPutRequest.spec (GF := GF) (hG := hG) := by
  intro r o
  wp_start as #Hr
  ihave Hinit : (go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.v3rpcInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, ⟨#HeK, -, #HeV, #HeL, -, -, -⟩, -, -⟩
  iunfold txn.putRequestIs at Hr
  icases Hr with ⟨%Hrn, %ksl, %vsl, %k, %v, %lease, %pk, %iv, %il, #Hk, #Hks, #Hv, #Hvs, #Hl, -, #Hiv, #Hil, -, %Ho⟩
  ihave %Hkl := ownSlice_len _ _ _ $$ Hks
  ihave %Hvl := ownSlice_len _ _ _ $$ Hvs
  subst Ho
  iunfold go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.errVarSet at HeK HeV HeL
  icases HeK with ⟨%eK, #HeK⟩
  icases HeV with ⟨%eV, #HeV⟩
  icases HeL with ⟨%eL, #HeL⟩
  wp_auto
  wp_if_destruct
  · iapply HΦ
    have hk : k = [] := by
      apply List.eq_nil_of_length_eq_zero; word
    simp only [v3rpc.putCheck, txn.putOpOf, hk, ↓reduceIte]
    unfold v3rpc.checkRes txn.errVarIs v3rpc.CheckErr.var
    iexists eK; iframe HeK; itrivial
  have hk : k ≠ [] := by
    intro h; subst h; simp at Hkl; word
  have hv : (v = []) ↔ vsl.len = W64 0 := by
    constructor
    · intro h; subst h; simp at Hvl; word
    · intro h; apply List.eq_nil_of_length_eq_zero; rw [Hvl.1, h]; rfl
  cases iv <;> cases il <;> wp_auto
  · iapply HΦ; v3rpc_put_fin
  · wp_if_destruct
    · iapply HΦ; v3rpc_put_fin
    · iapply HΦ; v3rpc_put_fin
  · wp_if_destruct
    · iapply HΦ; v3rpc_put_fin
    · iapply HΦ; v3rpc_put_fin
  · wp_if_destruct
    · (try wp_auto)
      wp_if_destruct
      · iapply HΦ; v3rpc_put_fin
      · iapply HΦ; v3rpc_put_fin
    · iapply HΦ; v3rpc_put_fin

end proof

end EtcdGrove
end Perennial
