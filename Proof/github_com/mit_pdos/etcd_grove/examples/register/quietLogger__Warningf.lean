/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/register/quietLogger__Warningf.lean`. Lean-first
(no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.register.quietLogger__Warningf

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace register

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]

theorem quietLogger.Warningf.wp_proof : quietLogger.Warningf.spec (GF := GF) (hG := hG) := by
  intro format args
  wp_start
  wp_auto
  wp_end

end proof

end register
end EtcdGrove
end Perennial
