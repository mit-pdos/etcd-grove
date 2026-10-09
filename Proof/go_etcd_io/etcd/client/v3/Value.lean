/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Value.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Value
public import Proof.go_etcd_io.etcd.client.v3.InvCmpTypes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Value.wp_proof : Value.spec (GF := GF) (hG := hG) := by
  intro key
  wp_start
  iapply wp_fupd
  wp_auto
  wp_apply wp_string_to_bytes key as %ksl ⟨Hks, -⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ «$v0»
  iStructNamed «$v0»
  ipersist Hks
  ipersist Result
  ipersist Target
  ipersist Key
  ipersist RangeEnd
  ipersist TargetUnion
  imodintro
  iapply HΦ
  unfold cmpAt compareAt compareUnionAt
  dsimp only [cmpKeyM, CmpTarget.code, CmpOp.code]
  rw [show (W32 0 : w32) = 0 from rfl]
  isplitl []
  · ipureintro; exact Hnn
  iexists ksl, slice.nil, GoInterface.nil
  iframe #
  isplitl []
  · iapply ownSlice_nil
  ileft; ipureintro; simp

end proof

end EtcdGrove
end Perennial
