/-
The proof of `types.IDSlice.Len` (`id.go`; claim #34, stage 2, 2026-11-25), the sort of
`membership.RaftCluster.MemberIDs`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.types.IDSlice__Len

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
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.types.Assumptions]

theorem types.IDSlice.Len.wp_proof :
    types.IDSlice.Len.spec (GF := GF) (hG := hG) := by
  intro sl ids dq
  wp_start as Hs
  wp_auto
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  have : sl.len = W64 (ids.length : Int) := by
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
