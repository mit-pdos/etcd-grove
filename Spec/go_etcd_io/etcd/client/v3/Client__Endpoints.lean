/-
`c.Endpoints()` (`client/v3/client.go`; unit P3a): a copy of the endpoints, read under `c.epMu`'s
read lock. (Item 5, client construction, 2026-10-17: the copy is a new slice, of the endpoints
`c.endpoints` holds when they are fixed: `dialWithBalancer` reads its first.) (prove-ps2-clientrdlock,
2026-11-24, decision 1b: proved over its body; the caller lends it a level-0 thread token, with
which it borrows a reader slot of `epMu`, `retryClientOk`'s `clientEpPool`. Until then a
trust-boundary axiom: a persistent interceptor held no reader slot.)
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `c.Endpoints()` on a client `clientv3.New` built returns some slice (a fresh copy), given and
giving back a level-0 thread token (`levelTok 0`: the reader slot's loan). -/
abbrev Client.Endpoints.spec : Prop :=
  ∀ (c : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryClientOk c ∗ levelTok 0 }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"Endpoints"))
      (Val #()))
  {{ (sl : GoSlice), RET #sl; levelTok 0 ∗ ∃ eps : List GoString, sl ↦* eps ∗
      -- (item 5) the endpoints, when the field and its slice are read-only
      (∀ (esl : GoSlice) (eps0 : List GoString),
        structFieldRef go_etcd_io.etcd.client.v3.Client go!"endpoints" c ↦□ esl -∗
        esl ↦*□ eps0 -∗ ⌜eps = eps0⌝) }}

end spec

end EtcdGrove
end Perennial
