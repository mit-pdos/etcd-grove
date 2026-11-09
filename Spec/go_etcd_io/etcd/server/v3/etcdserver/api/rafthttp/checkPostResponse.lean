/-
## `checkPostResponse(lg, resp, body, req, to)`

**Users.** `pipeline.post`, `snapshotSender.post`.

**Proof sketch.** The status switch; `strings.TrimSuffix`, the errors' `Error()`; `Header.Get` on the response and the request (read-only); `http.StatusText`, `url.URL.String`, `fmt.Errorf` (errors with `errOk`).

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour.

**Margin.** The error's kind is not stated.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Rafthttp

open Iris Iris.BI Raft
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) **Maps a POST's response**: `nil` exactly for `204`; an error otherwise (`errIncompatibleVersion`, `ErrClusterIDMismatch` on a `412` with their bodies, `errMemberRemoved` on a `403`, another). -/
def checkPostResponse.spec : Prop :=
  ∀ (lg : Loc) (resp : Loc) (st : w64) (hc : List (GoString × GoString)) (rd : GoInterface) (body : GoSlice) (bs : List w8) (dq : DFrac) (req : Loc) (R : Http.HReq) (to : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ (⌜lg = null⌝ ∨ Zap.isLogger lg) ∗ Http.respAt resp st hc rd ∗ body ↦*{dq} bs ∗ Http.reqRO req R }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.checkPostResponse)) (Val #lg)) (Val #resp)) (Val #body)) (Val #req)) (Val #to))
  {{ (err : GoInterface), RET #err; body ↦*{dq} bs ∗ ((⌜err = interface.nil ∧ uint.nat st = 204⌝) ∨ (⌜err ≠ interface.nil⌝ ∗ Http.errOk err)) }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
