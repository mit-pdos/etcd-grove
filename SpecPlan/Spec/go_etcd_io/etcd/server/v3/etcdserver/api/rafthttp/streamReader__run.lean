/-
## `(*streamReader).run()`

**Users.** `streamReader.start` (forked).

**Proof sketch.** `dial`, `decodeLoop`, `errors.Is`, `transport.IsClosedConnError` (trust), `rate.Limiter.Wait` (trust: returns or the context's error), `ctx.Err()`; `close(done)` when cancelled. `types.ID`'s `String()` on an addressable `ID` (log fields, headers) is 1c's `Types.ID.String_ptr.spec` (Goose's pointer receiver).

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour. verify-round (second pass): the sketch cites `Types.ID.String_ptr.spec`.

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

/-- (internal; a goroutine) **The reader loop**: dial, decode until the stream breaks, wait for the rate limiter, until stopped (`done` closed). -/
def streamReader.run.spec : Prop :=
  ∀ (cr : Loc) (ν : Net GF) (lid pid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ srAt cr ν lid pid ∗ srRun cr }}
    (App (Val (cr @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamReader.ty @!! go!"run")) (Val #()))
  {{ RET #(); True }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
