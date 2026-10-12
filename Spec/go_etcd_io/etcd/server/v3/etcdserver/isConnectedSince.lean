/-
`isConnectedSince`: the trust boundary (the server's `util.go` is names-only: it asks the transport (rafthttp, names-only)). Lean-first (no Rocq counterpart); the request path
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

/-- `isConnectedSince(transport, since, remote)`: some boolean (whether the transport has been
active with `remote` since `since`; `parseProposeCtxErr` only classifies its error by it). -/
abbrev isConnectedSince.spec : Prop :=
  ∀ (tr : GoInterface) (since : time.Time) (remote : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.isConnectedSince)) (Val #tr)) (Val #since)) (Val #remote))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
