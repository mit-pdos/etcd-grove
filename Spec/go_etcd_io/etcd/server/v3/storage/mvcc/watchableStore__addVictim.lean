/-
`(*watchableStore).addVictim(victim)` (internal; under `s.mu`): a non-empty batch appended to
`victims`, `victimc` signalled without blocking.

**Proof sketch.** `append`; a `select` with a `default` on the buffered `victimc`.
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

def watchableStore.addVictim.spec : Prop :=
  ∀ (s : Loc) (γ : MvccName) (wb : GoMap) (B : WBatch),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wsInv s γ ∗ wsMu s γ ∗ wbOwn wb B }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"addVictim")) (Val #wb))
  {{ RET #(); wsMu s γ }}

end spec

end Mvcc
end EtcdGrove
end Perennial
