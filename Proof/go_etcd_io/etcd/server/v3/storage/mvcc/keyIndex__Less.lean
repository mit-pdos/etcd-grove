/-
Proof of `Spec/.../mvcc/keyIndex__Less.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.keyIndex__Less
public import Perennial.Proof.bytes
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

/-- `bytes.Compare` returns `-1` exactly on Go's `<`. -/
theorem compareResult_eq_neg1 (a b : GoString) :
    decide (bytes.compareResult a b = W64 (-1)) = decide (go.GoStringLt a b) := by
  apply decide_eq_decide.2
  unfold bytes.compareResult
  split
  · rename_i h; exact ⟨fun _ => h, fun _ => rfl⟩
  · rename_i h
    constructor
    · intro h'
      split at h' <;> exact absurd h' (by decide)
    · intro h'; exact absurd h' h

theorem mvcc.keyIndex.Less.wp_proof : mvcc.keyIndex.Less.spec (GF := GF) (hG := hG) := by
  intro a b ka kb
  wp_start as ⟨#Hka, #Hkb⟩
  iunfold mvcc.kiKey at Hka
  iunfold mvcc.kiKey at Hkb
  icases Hka with ⟨%ksa, #Hpa, #Hsa⟩
  icases Hkb with ⟨%ksb, #Hpb, #Hsb⟩
  wp_auto
  wp_apply (bytes.wp_Compare ksa ksb DFrac.discard DFrac.discard ka kb) $$ [$Hsa $Hsb] as ⟨-, -⟩
  rw [compareResult_eq_neg1]
  wp_end

end proof

end EtcdGrove
end Perennial
