/-
`(*types.ID).String`, the pointer-receiver wrapper Go generates for the value method `ID.String`
(`x.String()` on an addressable `ID`, as `NewServer`'s on `b.cluster.nodeID`): the trust boundary
(`client/pkg/v3/types` is names-only, so the translation does not relate the two). Lean-first (no
Rocq counterpart); unit N4 (2026-10-17).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `p.String()` loads the `ID` at `p` (read at any fraction, kept) and returns `(*p).String()`,
some string (a hexadecimal rendering). -/
abbrev types.ID.String_ptr.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (id : go_etcd_io.etcd.client.pkg.v3.types.ID),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types ∗ p ↦{dq} id }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.types.ID.ty @!! go!"String"))
      (Val #()))
  {{ (s : GoString), RET #s; p ↦{dq} id }}

end spec

end EtcdGrove
end Perennial
