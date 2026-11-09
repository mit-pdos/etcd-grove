/-
`t.Lock()` (`batch_tx.go:109-112`): translated; internal (the embedded receiver of
`batchTxBuffered.Lock`). `ValidateCalledInsideUnittest` (off: `envOk`), `lock()`. Changes: as
`batchTxBuffered.Lock`. Margin: none.

**Changes** (verify-round: A10-provability B1): the post also gives the session's turn
`beTurn γ` (exclusive), which `Unlock`'s second update takes back: a client parks it with what it
took out at the lock, so that a later session refutes a stale parked state (`beTurn_excl`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`t.Lock()`** on the embedded `batchTx`: as `batchTxBuffered.Lock`. -/
def batchTx.Lock.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk ∗ beOpen γ q }}
    (App (Val ((bt0Loc γ) @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.batchTx.ty @!! go!"Lock")) (Val #()))
  {{ RET #(); ∃ I : Image, beSess γ q Fp.none (Sess.init I) ∗ beTurn γ ∗ Pk }}

end spec

end Backend
end EtcdGrove
end Perennial
