/- Lean-first (no Rocq counterpart).

`Main()` (`examples/mvccrand/mvccrand.go`): `Run` at seed 1, 1000 writer operations, 4 readers of
200 reads and 8 watchers, over a backend in the file `mvccrand.db`. **It returns** (every check of
mvcc passes; 2026-11-08, for the closed theorem). The premises are `Run`'s at that configuration:
the file `mvccrand.db` fresh (`fileHolds … ∅`), the thread and receipt bounds,
`dbOpenOk`, `dbCloseOk`, `ETCD_VERIFY` off (until premise fixes 5, 2026-11-10, also `keySized`, now
proved: `mvcc.keySized_all`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.Run

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc mvcc.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 38)],
  backend.dbOpenOk → backend.dbCloseOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand ∗
      backend.fileHolds go!"mvccrand.db" ∅ ∗
      threadTok ∗ envVerifyOff }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccrand.Main)) (Val #()))
  {{ RET #(); True }}

end spec

end mvccrand
end EtcdGrove
end Perennial
