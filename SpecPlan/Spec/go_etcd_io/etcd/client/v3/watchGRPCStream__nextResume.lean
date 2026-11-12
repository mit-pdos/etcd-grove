/-
`(*watchGRPCStream).nextResume()`: drops the abandoned (`nil`) head slots of `resuming`; its head or `nil`. Users: `run`.
Internal (`WatchInternal.lean`'s vocabulary). **Changes** from `specs-ref`'s file of the same
name: restated over this branch's vocabulary (the old `isWGS`, `WEnv`, `watchSrvFacts` gone).
**Margin**: mirrors the code.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.WatchInternal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `s.nextResume()`. -/
def watchGRPCStream.nextResume.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (who : Principal) (r : RunM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ wgsRun s γ who r }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"nextResume")) (Val #()))
  {{ (ws : Loc), RET #ws; ∃ r' : RunM, wgsRun s γ who r' ∗
      ⌜r' = { r with resuming := r.resuming.dropWhile (fun x => decide (x = null)) } ∧
        ws = (r'.resuming.head?).getD null⌝ }}

end spec

end ClientV3
end EtcdGrove
end Perennial
