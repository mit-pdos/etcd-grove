/-
`newBatchTxBuffered(backend)` (`batch_tx.go:309-318`): translated; internal (in `newBackend`,
before the hooks are set). The struct, empty write buffer, `tx.Commit()` (nothing pending, no hook:
the first write and read transactions begun). Changes: over `btPhys`. Margin: none.
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

/-- **`newBatchTxBuffered(b)`**: the batch transaction, its first write transaction begun at the
committed image `I`. -/
def newBatchTxBuffered.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (I : Image),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ beRun γ ∗ btPhys γ I 0 0 }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.backend.newBatchTxBuffered)) (Val #b))
  {{ (t : Loc), RET #t; ⌜t = btLoc γ⌝ ∗ beRun γ ∗ btPhys γ I 0 0 }}

end spec

end Backend
end EtcdGrove
end Perennial
