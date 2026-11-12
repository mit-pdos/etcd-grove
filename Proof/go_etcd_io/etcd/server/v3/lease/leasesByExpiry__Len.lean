/-
Proof of `Spec/go_etcd_io/etcd/server/v3/lease/leasesByExpiry__Len.lean`. Lean-first (no Rocq
counterpart); the lease-read plan (2026-10-31), as `MembersByID.Len`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.leasesByExpiry__Len

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease lease

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

theorem lease.leasesByExpiry.Len.wp_proof :
    lease.leasesByExpiry.Len.spec (GF := GF) (hG := hG) := by
  intro sl ls dq
  wp_start as Hs
  wp_auto
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  have : sl.len = W64 (ls.length : Int) := by
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
