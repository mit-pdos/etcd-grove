/-
## `(*streamReader).dial(t)`

**Users.** `streamReader.run`.

**Proof sketch.** `pick`, the path (`endpoint`, `path.Join`, `ID.String`), `NewRequest(GET)`, the headers (`X-Raft-To` the peer, `X-Server-From` the local id), `setPeerURLsHeader`, `WithContext`; the reader's fresh token map registered under a fresh name `τ` (`raftProto`'s request knowledge: a stream `GET` of `lid`'s reader); `RoundTrip` (no ticket: a `GET`); `serverVersion` of the response's headers (`raftProto` commits a parsable `X-Server-Version` with every response of a member's handler: no panic), `compareMajorMinorVersion`, `checkStreamSupport`; the status switch (`GracefulClose`, `ReadAll`, the `412` bodies, `reportCriticalError`, `fmt.Errorf`); `200`: the body with the reader's tokens (`streamBody`). `types.ID`'s `String()` on an addressable `ID` (log fields, headers) is 1c's `Types.ID.String_ptr.spec` (Goose's pointer receiver).

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour. verify-round (brief item 3): the package's error variables' values come from `vars_init.spec` (each `errIs g e`, non-nil, `Http.errOk`; pairwise distinct by `errVars_distinct.spec`), not from Lean constants; statement unchanged. The `X-Server-Version` premise of the old spec is now `raftProto`'s response header knowledge. verify-round (second pass): the sketch cites `Types.ID.String_ptr.spec`.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api

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

/-- (internal) **Dials the peer's stream** of type `t`: the `200` response's body (`streamBody`), or an error (a refused or failed dial; `errMemberRemoved` on `410`, reported on `errorc`). -/
def streamReader.dial.spec : Prop :=
  ∀ (cr : Loc) (ν : Net GF) (lid pid : w64) (t : StreamTy),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ srAt cr ν lid pid ∗ srRun cr }}
    (App (Val (cr @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamReader.ty @!! go!"dial")) (Val #(t.str)))
  {{ (rc : GoInterface) (err : GoInterface), RET (PairV #rc #err); srRun cr ∗ ((⌜err = interface.nil⌝ ∗ streamBody rc ν lid pid t) ∨ (⌜err ≠ interface.nil⌝ ∗ Http.errOk err)) }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
