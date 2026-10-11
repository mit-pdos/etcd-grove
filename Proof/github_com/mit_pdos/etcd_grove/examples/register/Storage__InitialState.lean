/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/register/Storage__InitialState.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.register.Storage__InitialState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

theorem Storage.InitialState.wp_proof : Storage.InitialState.spec (GF := GF) (hG := hG) := by
  intro s vsl
  wp_start as #Hv
  wp_auto
  iapply HΦ
  itrivial

end proof

end register
end EtcdGrove
end Perennial
