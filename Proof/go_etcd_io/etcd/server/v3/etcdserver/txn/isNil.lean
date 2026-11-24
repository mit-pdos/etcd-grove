/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart); unit P4 (2026-10-14).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.isNil
public import Perennial.Spec.reflect.ValueOf
public import Perennial.Spec.reflect.Value__IsNil
public import Perennial.Proof.reflect.Values

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.isNil.wp_proof
    (hV : _root_.Perennial.reflect.ValueOf.spec (GF := GF) (hG := hG))
    (hN : _root_.Perennial.reflect.Value.IsNil.spec (GF := GF) (hG := hG)) :
    txn.isNil.spec (GF := GF) (hG := hG) := by
  intro T p
  wp_start
  wp_auto
  wp_apply (hV.1 (t := go.PointerType T) 22 #p rfl (by simp [_root_.Perennial.reflect.rtype.ty]) (by omega))
  wp_apply (hN.1 _ (t := go.PointerType T) (e := T) p (by simp only; rfl) (by simp only; rfl) rfl)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
