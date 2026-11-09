/-
`clientv3.OpCompact` (`client/v3/compact_op.go`).

Users: `kv.Compact`.

Proof sketch: `CompactOp.applyCompactOpts.spec` on `CompactOp{rev}`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/OpCompact.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Api

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

/-- `OpCompact(rev, opts...)`: the revision and `physical` as the options set it. -/
def OpCompact.spec : Prop :=
  ∀ (rev : w64) (sl : GoSlice) (gs : List (CompactOpM → CompactOpM)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ compactOptsAt sl gs }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.OpCompact)) (Val #rev)) (Val #sl))
  {{ (op : go_etcd_io.etcd.client.v3.CompactOp), RET #op; compactOptsAt sl gs ∗
      ⌜let m := gs.foldl (fun (o : CompactOpM) (g : CompactOpM → CompactOpM) => g o)
          { revision := rev, physical := false };
        op.revision' = m.revision ∧ op.physical' = m.physical⌝ }}

end spec

end ClientV3
end EtcdGrove
end Perennial
