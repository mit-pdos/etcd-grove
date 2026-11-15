/-
`NewDemux` (`cache/*.go`), an internal helper.
Users: `newCache`.
Proof sketch: `newDemux.spec`; `wg.Add(1)` and the resync loop's goroutine (`demux.resyncLoop.spec`) under the wait group's protocol (`wgAddOk`).
Changes: restated over the opaque vocabulary of `Internal.lean` (the old internal handles, ghost names and certificate parameters replaced by predicates over W0's model); the spec mirrors the code.
Margin: none known.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.cache.v3.Internal

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

/-- `NewDemux(ctx, wg, historyWindowSize, resyncInterval)`. -/
def NewDemux.spec : Prop :=
  ∀ (γ : Cluster) (pfx : GoString) (s : Loc) (ctx : GoInterface) (wg : Loc) (hws : w64)
    (ri : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ Context.ctxOk ctx ∗ wgAddOk wg ∗ ⌜0 < sint.Z hws ∧ sint.Z hws ≤ 2 ^ 61⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.cache.v3.NewDemux)) (Val #ctx)) (Val #wg)) (Val #hws)) (Val #ri))
  {{ (d : Loc), RET #d; isDemux d γ pfx s ∗ demuxFeed d γ pfx s none }}

end spec

end Cache
end EtcdGrove
end Perennial
