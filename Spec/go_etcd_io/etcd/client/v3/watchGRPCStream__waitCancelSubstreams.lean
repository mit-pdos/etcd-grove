/-
`(*watchGRPCStream).waitCancelSubstreams(stopc)`: one goroutine per resuming substream, until `stopc` closes: a closing one's `outc` closed if its context is done; a live one whose context ends meanwhile marked closing, `outc` closed, sent on `closingc` by a goroutine of `s.wg`. `donec` closes when all are done (`wcsPending_join`). Users: `newWatchClient`.
Internal (`WatchInternal.lean`'s vocabulary). **Changes** from `specs-ref`'s file of the same
name: restated over this branch's vocabulary (the old `isWGS`, `WEnv`, `watchSrvFacts` gone).
**Margin**: mirrors the code.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.WatchInternal

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

/-- `s.waitCancelSubstreams(stopc)`. -/
def watchGRPCStream.waitCancelSubstreams.spec : Prop :=
  ∀ (s w : Loc) (γ : Cluster) (who : Principal) (r : RunM) (stopc : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ wgsAt s w γ who ∗ wgsRun s γ who r ∗ wcsStop s stopc }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"waitCancelSubstreams")) (Val #stopc))
  {{ (donec : Loc), RET #donec; wcsPending s γ who r stopc donec false }}

end spec

end ClientV3
end EtcdGrove
end Perennial
