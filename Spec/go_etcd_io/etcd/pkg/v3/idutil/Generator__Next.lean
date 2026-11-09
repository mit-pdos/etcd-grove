/-
## `(*Generator).Next()`

**Users.** `processInternalRaftRequestOnce` (`v3_server.go:1068`: the request's `Header.ID`, the
wait registry's key), `LeaseGrant` (`v3_server.go:438`: a lease id when the client asks for `0`),
the read loop (`read.go:150`, through `EtcdServer.NextRequestID`: the read index's context),
`configure` (`server.go:1781`: a conf change's id). Concurrent callers (any goroutine). Snippet:
`examples/specreq/wait/idutil.go`.

**Proof sketch.** `atomic.AddUint64(&g.suffix, 1)` (Perennial's atomic add, with its time receipt:
fewer than `2 ^ 48` increments in a run), `lowbit(suffix, 48)`, the prefix read-only; the generator's
invariant records the id as issued (`idFresh`). Freshness across runs of one prefix is the trusted
model's (see `Api.lean`).

**Changes.** The old spec took a per-call credit (`idCred`) and gave the id's shape (prefix,
initial suffix, count): the shape went (no user reads it), the credit is the receipts' bound, at
its owner (the bounds plan), so no caller threads it.

**Margin.** The ids of one run are increasing modulo `2 ^ 48`: not exposed.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.idutil.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace IdUtil

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.idutil.Assumptions]

/-- **A fresh id** (never issued before in the id space, not `0`). -/
def Generator.Next.spec : Prop :=
  ∀ (g : Loc) (γi : IdSpace),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.idutil ∗ idGen g γi }}
    (App (Val (g @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.idutil.Generator.ty @!! go!"Next"))
      (Val #()))
  {{ (id : w64), RET #id; idFresh γi id }}

end spec
end IdUtil
end EtcdGrove
end Perennial
