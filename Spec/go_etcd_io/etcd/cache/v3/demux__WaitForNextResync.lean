/-
`demux.WaitForNextResync` (`cache/*.go`), an internal helper.
Users: `Cache.WaitForNextResync`.
Proof sketch: `notifier.wait.spec` on `d.resynced`.
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

/-- `d.WaitForNextResync(ctx)`. -/
def demux.WaitForNextResync.spec : Prop :=
  ∀ (d : Loc) (γ : Cluster) (pfx : GoString) (s : Loc) (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isDemux d γ pfx s ∗ Context.ctxOk ctx }}
    (App (Val (d @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.demux.ty @!! go!"WaitForNextResync")) (Val #ctx))
  {{ (err : GoInterface), RET #err;
      ⌜err = GoInterface.nil⌝ ∨ (Context.ctxDone ctx ∗ context.isCtxErr err) }}

end spec

end Cache
end EtcdGrove
end Perennial
