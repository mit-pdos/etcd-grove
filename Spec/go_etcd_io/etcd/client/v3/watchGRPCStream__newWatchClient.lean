/-
`(*watchGRPCStream).newWatchClient()`: every substream to resume (its id forgotten), their goroutines stopped (`resumec`) and joined, a new stream opened (`openWatchClient`) while watching for watches whose context ends (`waitCancelSubstreams`, `wcsPending_close`, `wcsPending_join`), a goroutine per non-closing substream, `serveWatchClient` forked on success. Users: `run`.
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

/-- `s.newWatchClient()`: the substreams all resuming, in `resuming`'s order then the registered
ones' (in the map's order); the new stream's sending half, or an error. -/
def watchGRPCStream.newWatchClient.spec : Prop :=
  ∀ (s w : Loc) (γ : Cluster) (who : Principal) (r : RunM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ wgsAt s w γ who ∗ wgsRun s γ who r }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"newWatchClient")) (Val #()))
  {{ (wc err : GoInterface), RET (PairV #wc #err); ∃ r' : RunM, wgsRun s γ who r' ∗
      ⌜r'.subs = [] ∧ r'.closeErr = r.closeErr ∧ r'.joined = false ∧
        ∃ l : List Loc, l.Perm (r.subs.map Prod.snd) ∧
          r'.resuming = r.resuming.filter (fun x => decide (x ≠ null)) ++ l⌝ ∗
      ((⌜err = GoInterface.nil⌝ ∗ wgsSend s γ who wc) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ ∃ k, callErr err k)) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
