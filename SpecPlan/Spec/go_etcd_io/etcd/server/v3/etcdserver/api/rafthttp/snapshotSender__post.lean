/-
## `(*snapshotSender).post(req)`

**Users.** `snapshotSender.send`.

**Proof sketch.** `WithCancel`, `WithContext`, a goroutine doing `RoundTrip` (with the request's knowledge and ticket), a `time.AfterFunc` closing the body on a timeout (`readerCloser`), `io.ReadAll`, a result channel of capacity 1; a `select` on `stopc` (`errStopped`) and the result; `checkPostResponse`.

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour. verify-round (brief item 3): the package's error variables' values come from `vars_init.spec` (each `errIs g e`, non-nil, `Http.errOk`; pairwise distinct by `errVars_distinct.spec`), not from Lean constants; statement unchanged.

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

/-- (internal) **Round-trips the snapshot request** (stopping on `stopc`): `nil` only for a `204`. -/
def snapshotSender.post.spec : Prop :=
  ∀ (s : Loc) (ν : Net GF) (lid pid : w64) (r : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ ssAt s ν lid pid ∗ snapReq r ν lid pid }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.snapshotSender.ty @!! go!"post")) (Val #r))
  {{ (err : GoInterface), RET #err; Http.errOk err }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
