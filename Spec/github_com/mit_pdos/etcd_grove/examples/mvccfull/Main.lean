/- Lean-first (no Rocq counterpart).

`Main()` (`examples/mvccfull/mvccfull.go`): `Run` with `MainConfig("mvccfull")`. **It returns** (every
check passes). The premises are `Run`'s at that configuration: its files fresh (`filePathsM` of
`mainConfigM`: they depend only on the prefix and `Ops`), the thread and receipt bounds,
`ckptEffectsOk`, `dbOpenOk`, `dbCloseOk`, `ETCD_VERIFY` off (until premise fixes 5, 2026-11-10, also
`keySized`, now proved: `mvcc.keySized_all`). `MainConfig`'s configuration
is in `Run`'s scope (`runCfgOk`): its read weights `[1, 1, 2, 1, 1, 0]` give the hashes none
(`readMixOk`), `Ops = 12000`, 15 threads, the batch limits `3` and `2`, the 120 keys of depth `4`.
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
      threadTok ∗ envVerifyOff }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccfull.Main)) (Val #()))
  {{ RET #(); True }}

end spec

end mvccfull
end EtcdGrove
end Perennial
