/-
**`bootstrap.spec` implies its one-member restriction** (2026-11-24; `Spec/.../etcdserver/bootstrapOne.lean`):
`bootstrap.specOne` is `bootstrap.spec` under two more premises, so it is no stronger, and the interim
axiom `bootstrap.wp_proofOne` retires into `bootstrap.specOne_of_spec` of #34's linked result. A defs
module (it imports the two specs only). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrapOne

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section weaken
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [MemStorReg GF]

/-- **`bootstrap.spec` gives `bootstrap.specOne`**: the latter is the former under two more premises. -/
theorem bootstrap.specOne_of_spec (h : bootstrap.spec (GF := GF) (hG := hG)) :
    bootstrap.specOne (GF := GF) (hG := hG) := by
  intro i1 i2 cfg U γ N _ _
  exact @h i1 i2 cfg U γ N

end weaken

end EtcdGrove
end Perennial
