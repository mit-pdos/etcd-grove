/-
`(*watchableStore).rev()` (internal; `watchStream.Rev`'s callee): `s.store.Rev()` (3e's `store.Rev`:
`revMu`'s read side, the reader token): the committed revision, a prefix of the notified history.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.WatchInternal
public import SpecPlan.Spec.go_uber_org.zap.Api

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

def watchableStore.rev.spec : Prop :=
  ∀ (s : Loc) (γ : MvccName) (Q : MvccState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ wsInv s γ ∗ mvccReaders γ 1 ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅ <{ mvccState γ σ, COMM Q σ }> }}
    (App (Val (s @!! go.GoType.PointerType watchableStore.ty @!! go!"rev")) (Val #()))
  {{ (r : w64), RET #r; mvccReaders γ 1 ∗ ∃ σ : MvccState, Q σ ∗ ⌜r = W64 σ.rev⌝ }}

end spec

end Mvcc
end EtcdGrove
end Perennial
