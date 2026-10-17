/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/permSlice__Len.lean`. Lean-first (no Rocq counterpart; PR
etcd#21845, `pr-verify/etcd-21845`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.permSlice__Len


@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth go_etcd_io.etcd.api.v3 auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.permSlice.Len.wp_proof : auth.permSlice.Len.spec (GF := GF) (hG := hG) := by
  intro sl ps dq
  wp_start as Hs
  wp_auto
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  have : sl.len = W64 (ps.length : Int) := by
    rw [Hl.1]
    show sl.len = BitVec.ofInt 64 ((sint.Z sl.len).toNat : Int)
    rw [Int.toNat_of_nonneg Hl.2]
    exact BitVec.ofInt_toInt.symm
  rw [this]
  iapply HΦ
  iexact Hs

end proof

end EtcdGrove
end Perennial
