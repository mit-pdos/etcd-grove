/-
`(*clientv3.CompactOp).applyCompactOpts` (`client/v3/compact_op.go`).

Users: `OpCompact`.

Proof sketch: a loop: `compactOptAt_call`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/CompactOp__applyCompactOpts.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.Api

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

/-- `op.applyCompactOpts(opts)`: the options applied in order. -/
def CompactOp.applyCompactOpts.spec : Prop :=
  ∀ (p : Loc) (op : go_etcd_io.etcd.client.v3.CompactOp) (sl : GoSlice) (gs : List (CompactOpM → CompactOpM)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ p ↦ op ∗ compactOptsAt sl gs }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.CompactOp.ty @!! go!"applyCompactOpts")) (Val #sl))
  {{ RET #(); compactOptsAt sl gs ∗ ∃ op' : go_etcd_io.etcd.client.v3.CompactOp, p ↦ op' ∗
      ⌜let m := gs.foldl (fun (o : CompactOpM) (g : CompactOpM → CompactOpM) => g o)
          { revision := op.revision', physical := op.physical' };
        op'.revision' = m.revision ∧ op'.physical' = m.physical⌝ }}

end spec

end ClientV3
end EtcdGrove
end Perennial
