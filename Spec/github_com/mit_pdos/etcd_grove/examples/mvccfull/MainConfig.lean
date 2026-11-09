/- Lean-first (no Rocq counterpart).

`MainConfig(prefix)` (`examples/mvccfull/config.go`): `Main`'s configuration
(`mainConfigM`), its `Mix`'s seven weight slices fresh (owned, `mainMixOwn`), at the code's weights
(the read weights `[1, 1, 2, 1, 1, 0]`: no hash reads until F2).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull

section model
variable [GooseExts]

/-- `MainConfig(prefix)` with the `Mix` `mx` (whose slices `mainMixOwn` gives). -/
def mainConfigM (pfx : GoString) (mx : Mix) : Config :=
  { Prefix' := pfx, Ops' := W64 12000, Depth' := W64 4, MaxVal' := W64 5000, Readers' := W64 2,
    Reads' := W64 4000, Streams' := W64 2, Watchers' := W64 64, BatchLimit' := W64 3,
    BatchInterval' := W64 0, CompactionBatchLimit' := W64 2, CompactionSleep' := W64 1000,
    Mix' := mx }

end model

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

/-- `MainConfig`'s `Mix`: its weights, its pauses. -/
def mainMixOwn (mx : Mix) : IProp GF :=
  iprop(⌜mx.Pause' = W64 100000 ∧ mx.RecvPause' = W64 0⌝ ∗
    mx.Step' ↦* [W64 800, W64 160, W64 6, W64 3, W64 3, W64 28] ∗
    mx.Op' ↦* [W64 25, W64 12, W64 25, W64 5, W64 5, W64 10, W64 4, W64 10, W64 4] ∗
    mx.CompactAt' ↦* [W64 1, W64 1, W64 0] ∗
    mx.RangeRev' ↦* [W64 1, W64 1, W64 2, W64 0] ∗
    mx.Read' ↦* [W64 1, W64 1, W64 2, W64 1, W64 1, W64 0] ∗
    mx.Act' ↦* [W64 4, W64 1, W64 1, W64 1, W64 1, W64 1] ∗
    mx.Start' ↦* [W64 1, W64 3, W64 0])

/-- See the file header. -/
abbrev MainConfig.spec : Prop :=
  ∀ (pfx : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccfull.MainConfig)) (Val #pfx))
  {{ (mx : Mix), RET #(mainConfigM pfx mx); mainMixOwn mx }}

end spec

end mvccfull
end EtcdGrove
end Perennial
