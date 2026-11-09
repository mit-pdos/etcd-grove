/-
`realClock.NewTimer` (`cache/*.go`), an internal helper.
Users: `New` (the cache's clock), via the `Clock` bundle (`clockOk`).
Proof sketch: Perennial's `time.NewTimer`, boxed in a `*realTimer`.
Changes: restated over the opaque vocabulary of `Internal.lean` (the old internal handles, ghost names and certificate parameters replaced by predicates over W0's model); the spec mirrors the code.
Margin: none known.
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Cache

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `realClock{}.NewTimer(d)`: a timer. -/
def realClock.NewTimer.spec : Prop :=
  ∀ (rc : go_etcd_io.etcd.cache.v3.realClock) (d : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 }}
    (App (Val (rc @!! go_etcd_io.etcd.cache.v3.realClock.ty @!! go!"NewTimer")) (Val #d))
  {{ (tm : GoInterface), RET #tm; timerOk tm }}

end spec

end Cache
end EtcdGrove
end Perennial
