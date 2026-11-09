/- Lean-first (no Rocq counterpart).

`Main()` (`examples/mvccfull/mvccfull.go`): `Run` with `MainConfig("mvccfull")`. **It returns** (every
check passes). The premises are `Run`'s at that configuration: its files fresh (`filePathsM` of
`mainConfigM`: they depend only on the prefix and `Ops`), the thread and receipt bounds,
`ckptEffectsOk`, `keySized`, `dbOpenOk`, `dbCloseOk`, `ETCD_VERIFY` off.

**Not provable in F1** (reported): `MainConfig`'s read weights `[1, 1, 2, 1, 1, 2]` give the hashes
`2`, so `readMixOk` fails; the closed theorem moves to F2 (the plan's decision 1).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.Run
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.MainConfig

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- See the file header. -/
abbrev Main.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 38)],
  ckptEffectsOk → backend.dbOpenOk → backend.dbCloseOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗
      ([∗list] p ∈ filePathsM (mainConfigM go!"mvccfull" (zeroValDef : Mix)), backend.fileHolds p ∅) ∗
      □ (∀ (γB : backend.BNames) (P : backend.BParams) (b : Loc), keySized γB P b) ∗
      threadTok ∗ envVerifyOff }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccfull.Main)) (Val #()))
  {{ RET #(); True }}

end spec

end mvccfull
end EtcdGrove
end Perennial
