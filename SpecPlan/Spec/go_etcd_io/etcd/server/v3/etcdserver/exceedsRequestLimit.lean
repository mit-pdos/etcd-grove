/-
## `exceedsRequestLimit(applied, committed, r, enablePriority)` (`util.go:60-70`)

**Users.** `processInternalRaftRequestOnce` (2c: `ErrTooManyRequests`, a refusal).

**Proof sketch.** Two comparisons against `maxNormalGap`/`maxPriorityGap` (`uint64`, wrapping),
`isPriorityRequest`.

**Changes**: from `specs-ref`'s `exceedsRequestLimit.lean`. **Margin.** Any answer suffices to the
caller (a refusal is a `Step`), but the code's is stated: some boolean.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiBoot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`exceedsRequestLimit`**: some answer (the request path refuses on `true`). -/
def exceedsRequestLimit.spec : Prop :=
  ∀ (ai ci : w64) (r : Loc) (b prio : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ irrIsRevoke r b }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.exceedsRequestLimit)) (Val #ai)) (Val #ci)) (Val #r)) (Val #prio))
  {{ (x : Bool), RET #x; True }}

end spec

end EtcdServer
end EtcdGrove
end Perennial
