/-
`errors.Is`: the trust boundary (Perennial does not translate `errors.Is` (it uses `internal/reflectlite`)). Lean-first (no Rocq counterpart).

Stated under the `errors` package's assumptions (2026-10-12, the apply package's unit 2; it was
the server's): the server's `applyEntryNormal` and the apply package's `dispatch` (its deferred
metrics: `errors.Is(ar.Err, mvcc.ErrCompacted)` on any error) both use it. Perennial's
`errors.wp_Is` needs the error's tree (`errorIsTree`), which an error from a names-only component
does not come with.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3 go_etcd_io.etcd.pkg.v3 go_uber_org

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.errors.Assumptions]

/-- `errors.Is(err, target)` returns some boolean. -/
abbrev errors.Is.spec : Prop :=
  ∀ (err target : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.errors }}
    (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #err)) (Val #target))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
