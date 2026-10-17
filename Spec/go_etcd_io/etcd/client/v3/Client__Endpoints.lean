/-
`c.Endpoints()` (`client/v3/client.go`, names only; unit P3a): a copy of the endpoints, read
under `c.epMu`'s read lock (whose bounded reader slots a persistent interceptor cannot hold: the
reason it is not proved). (Item 5, client construction, 2026-10-17: the copy is a new slice,
of the endpoints `c.endpoints` holds when they are fixed: `dialWithBalancer` reads its first.)
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
  {{ (sl : GoSlice), RET #sl; ∃ eps : List GoString, sl ↦* eps ∗
      -- (item 5) the endpoints, when the field and its slice are read-only
      (∀ (esl : GoSlice) (eps0 : List GoString),
        structFieldRef go_etcd_io.etcd.client.v3.Client go!"endpoints" c ↦□ esl -∗
        esl ↦*□ eps0 -∗ ⌜eps = eps0⌝) }}

end spec

end EtcdGrove
end Perennial
