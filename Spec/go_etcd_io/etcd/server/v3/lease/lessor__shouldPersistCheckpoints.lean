/-
`(*lessor).shouldPersistCheckpoints` (`server/lease/lessor.go`). Lean-first (no Rocq
counterpart); see `Proof/go_etcd_io/etcd/server/v3/lease/InvLessor.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.lease lease

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- `le.shouldPersistCheckpoints()`: some boolean (the configuration's `checkpointPersist`, or the
cluster at v3.6 or later). -/
abbrev lease.lessor.shouldPersistCheckpoints.spec : Prop :=
  ∀ (lp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ lessorCfg lp }}
    (App (Val (lp @!! go.GoType.PointerType lessor.ty @!! go!"shouldPersistCheckpoints"))
      (Val #()))
  {{ (r : Bool), RET #r; True }}

end spec

end EtcdGrove
end Perennial
