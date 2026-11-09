/-
`watcherBatch.add(w, ev)` (internal): the event added to `w`'s batch (a new one if none).

**Proof sketch.** The map lookup, `&eventBatch{}`, `eventBatch.add`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.WatchInternal
public import Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI EtcdModel EtcdWire go_etcd_io.etcd.server.v3.storage.mvcc Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

def watcherBatch.add.spec : Prop :=
  ∀ (wb : GoMap) (B : WBatch) (w p : Loc) (e : EvM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wbOwn wb B ∗ evOwn p e ∗ ⌜wb ≠ null⌝ }}
    (App (App (Val (wb @!! watcherBatch.ty @!! go!"add")) (Val #w)) (Val #p))
  {{ RET #(); wbOwn wb (B.add w e) }}

end spec

end Mvcc
end EtcdGrove
end Perennial
