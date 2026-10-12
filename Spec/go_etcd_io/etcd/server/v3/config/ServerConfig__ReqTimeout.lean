/-
`config.ServerConfig.ReqTimeout`: the trust boundary (`server/v3/config` is names-only). Lean-first (no Rocq counterpart); the request path
(`notes/decisions.md`, "The request path").
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply

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

/-- `c.ReqTimeout()` (`5s + 2 * ElectionTicks * TickMs`): some duration (the proposal's timeout,
which the model does not read), on a non-nil config. -/
abbrev config.ServerConfig.ReqTimeout.spec : Prop :=
  ∀ (c : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config ∗ ⌜c ≠ null⌝ }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.config.ServerConfig.ty @!! go!"ReqTimeout"))
      (Val #()))
  {{ (d : time.Duration), RET #d; True }}

end spec

end EtcdGrove
end Perennial
