/-
`(*readView).Rev()` (`kv_view.go:32`): `rv.kv.Read(SharedBufReadTxMode, traceutil.TODO())`, its
`Rev()`, its `End()`. Internal: the body of the store's promoted `Rev` (`KV.Rev.contract`); no client
holds a view. Proof sketch: with a reader token, `KV.Read.contract` at `kv` (the update fires at the
read; 4b's `TODO()` gives a fresh trace), `Txn.Rev.contract`, `Txn.End.contract` (`.read`: the token
back), through `shapes`. With the `Rev` right (`revRd γ true`: integration Y, persistent, with the
caller's `threadTok`): the same code over the store's realization (`isMvcc kv γ` gives `isStore`):
the thread token buys one of the `Rev` pool's lock-only slots for the call (`s.mu`, `revMu`, the
shared `ReadTx`'s bare `RLock`/`RUnlock` rows, `kbBareSlot`), the revisions read under `revMu` (the
update fires there), the slot back at `End`.

**Changes** from `specs-ref`'s file: `KV.Rev.contract`'s statement at the view's store.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `KV.Rev`'s behaviour for the store the view reads. -/
def readView.Rev.spec : Prop :=
  ∀ (rv : Loc) (kv : GoInterface) (γ : MvccName) (rt : Bool) (Q : MvccState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      rv.[readView, go!"kv"] ↦□ kv ∗ isMvcc kv γ ∗ revRd γ rt ∗
      AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅ <{ mvccState γ σ, COMM Q σ }> }}
    (App (Val (rv @!! go.GoType.PointerType readView.ty @!! go!"Rev")) (Val #()))
  {{ (r : w64), RET #r; revRd γ rt ∗ ∃ σ : MvccState, Q σ ∗ ⌜r = W64 σ.rev⌝ }}

end spec
end Mvcc
end EtcdGrove
end Perennial
