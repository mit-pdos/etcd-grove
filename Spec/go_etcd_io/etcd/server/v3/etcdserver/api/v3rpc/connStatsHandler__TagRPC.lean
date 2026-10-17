/-
`(*connStatsHandler).TagRPC` (`connstats.go`, pr-verify etcd#21621): part of grpc's
`stats.Handler` interface. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvConnStats

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`h.TagRPC(ctx, info)`** returns `ctx`. -/
abbrev v3rpc.connStatsHandler.TagRPC.spec : Prop :=
  ∀ (h : Loc) (ctx : GoInterface) (s : Loc),
  {{ (True : IProp GF) }}
    (App (App (Val (h @!! go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.connStatsHandler.ty @!! go!"TagRPC"))
      (Val #ctx)) (Val #s))
  {{ RET #ctx; True }}

end spec

end EtcdGrove
end Perennial
