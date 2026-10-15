/-
`c.Endpoints()` (`client/v3/client.go`, names only; unit P3a): a copy of the endpoints, read
under `c.epMu`'s read lock (whose bounded reader slots a persistent interceptor cannot hold: the
reason it is not proved).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvRetry

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk)

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `c.Endpoints()` on a client `clientv3.New` built returns some slice (a fresh copy). -/
abbrev Client.Endpoints.spec : Prop :=
  ∀ (c : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryClientOk c }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"Endpoints"))
      (Val #()))
  {{ (sl : GoSlice), RET #sl; True }}

end spec

end EtcdGrove
end Perennial
