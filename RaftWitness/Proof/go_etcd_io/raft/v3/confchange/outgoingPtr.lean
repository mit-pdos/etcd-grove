/-
Proof of `Spec/go_etcd_io/raft/v3/confchange/outgoingPtr.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.outgoingPtr

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem confchange.outgoingPtr.wp_proof :
    confchange.outgoingPtr.spec (GF := GF) (hG := hG) := by
  intro vp
  wp_start as _
  wp_auto
  rw [show sint.Z (W64 1) = (1 : Int) by decide]
  wp_end

end proof

end EtcdGrove
end Perennial
