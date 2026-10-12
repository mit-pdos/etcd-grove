/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.compareKV
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.compareInt64

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.server.v3.storage.mvcc go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.compareResult_bytesCmp (a b : GoString) :
    bytes.compareResult a b = W64 (bytesCmp a b) := by
  unfold bytes.compareResult bytesCmp cmpSign
  by_cases h1 : go.GoStringLt a b
  · simp [h1]
  · by_cases h2 : a = b
    · subst h2; simp only [h1, ↓reduceIte]; rfl
    · simp [h1, h2]

theorem txn.cmpSign_eq (l e : Bool) {inst : Decidable (W64 (cmpSign l e) = W64 0)} :
    CmpOp.holds .eq (cmpSign l e) = @decide _ inst := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  cases l <;> cases e <;> simp [CmpOp.holds, cmpSign] <;> decide

theorem txn.cmpSign_neq (l e : Bool) {inst : Decidable (W64 (cmpSign l e) = W64 0)} :
    CmpOp.holds .neq (cmpSign l e) = !(@decide _ inst) := by
  rw [← txn.cmpSign_eq l e]
  cases l <;> cases e <;> simp [CmpOp.holds, cmpSign]

theorem txn.cmpSign_gt (l e : Bool) {inst : Decidable (sint.Z (W64 0) < sint.Z (W64 (cmpSign l e)))} :
    CmpOp.holds .gt (cmpSign l e) = @decide _ inst := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  cases l <;> cases e <;> simp [CmpOp.holds, cmpSign] <;> decide

theorem txn.cmpSign_lt (l e : Bool) {inst : Decidable (sint.Z (W64 (cmpSign l e)) < sint.Z (W64 0))} :
    CmpOp.holds .lt (cmpSign l e) = @decide _ inst := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  cases l <;> cases e <;> simp [CmpOp.holds, cmpSign] <;> decide

/-- Close `Φ #(cmpKv ..) = Φ #(the Go expression)`. -/
macro "txn_cmp_close" : tactic => `(tactic| (
  congr 2
  simp only [cmpKv, int64Cmp, bytesCmp, txn.compareResult_bytesCmp]
  first
  | exact txn.cmpSign_eq _ _
  | exact txn.cmpSign_neq _ _
  | exact txn.cmpSign_gt _ _
  | exact txn.cmpSign_lt _ _))

set_option maxHeartbeats 1600000 in
theorem txn.compareKV.wp_proof
    (hCmp : txn.compareInt64.spec (GF := GF) (hG := hG)) :
    txn.compareKV.spec (GF := GF) (hG := hG) := by
  intro c ckv cm v
  wp_start as ⟨#Hc, #Hkv⟩
  iunfold txn.compareIs at Hc
  icases Hc with ⟨%Hcn, %ksl, %esl, %e, %u, #Hres, #Htgt, #Hk, #Hks, #He, #Hes, %Hre, #Hu, #Hun, %Hw⟩
  -- the operand's wrapper is not a typed `nil` (`compareIs`): `tv != nil` holds
  have hw : ∀ (t : go.GoType) (w : Loc), u = interface.mkOk t #w → w ≠ null := Hw
  iunfold txn.kvIs at Hkv
  icases Hkv with ⟨%keySl, %valSl, #HK, #HKs, #HC, #HM, #HV, #HVl, #HVs, #HL⟩
  ihave #Hnil := ownSlice_nil (V := w8) (GF := GF) DFrac.discard
  rcases cm with ⟨key, re, target, op, num, val⟩
  cases target
  case value =>
    cases op
    all_goals
      simp only [CmpTarget.code, CmpOp.code, compareUnionAt] at *
      wp_auto
      icases Hun with (⟨%Hu0, %Hn0⟩ | ⟨%w, %vsl, %Hu0, #Hw, #Hvs⟩)
      · subst Hu0 Hn0
        wp_auto
        wp_apply (bytes.wp_Compare valSl slice.nil DFrac.discard DFrac.discard v.value [])
          $$ [$HVs $Hnil] as -
        ihave H := HΦ $$ []
        · itrivial
        iExactEq H
        txn_cmp_close
      · have hwn := hw _ w Hu0
        subst Hu0
        wp_auto
        rw [decide_eq_false hwn]
        wp_auto
        wp_apply (bytes.wp_Compare valSl vsl DFrac.discard DFrac.discard v.value val)
          $$ [$HVs $Hvs] as -
        ihave H := HΦ $$ []
        · itrivial
        iExactEq H
        txn_cmp_close
  all_goals
    cases op
    all_goals
      simp only [CmpTarget.code, CmpOp.code, compareUnionAt] at *
      wp_auto
      icases Hun with (⟨%Hu0, %Hn0⟩ | ⟨%w, %Hu0, #Hw⟩)
      · subst Hu0 Hn0
        wp_auto
        wp_apply hCmp
        ihave H := HΦ $$ []
        · itrivial
        iExactEq H
        txn_cmp_close
      · have hwn := hw _ w Hu0
        subst Hu0
        wp_auto
        rw [decide_eq_false hwn]
        wp_auto
        wp_apply hCmp
        ihave H := HΦ $$ []
        · itrivial
        iExactEq H
        txn_cmp_close

end proof

end EtcdGrove
end Perennial
