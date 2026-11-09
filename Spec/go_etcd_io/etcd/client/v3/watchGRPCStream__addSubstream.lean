/-
`(*watchGRPCStream).addSubstream(resp, ws)`: a `Created` answering `resuming`'s head `ws`: refused (id `-1`, or canceled with a reason) sets `closeErr` (`rpctypes.Error(errors.New(reason))`) and closes `ws.recvc`; else registers `ws` under the id. Users: `run`.
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

/-- `s.addSubstream(resp, ws)`. -/
def watchGRPCStream.addSubstream.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (who : Principal) (r : RunM) (p : Loc) (dq : DFrac)
    (mr : WireWatchRespM) (ws : Loc) (rest : List Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ wgsRun s γ who r ∗ wireWatchRespOwn p dq mr ∗
      ⌜mr.created = true ∧ r.resuming = ws :: rest⌝ }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"addSubstream")) (Val #p)) (Val #ws))
  {{ RET #(); wireWatchRespOwn p dq mr ∗ ∃ r' : RunM, wgsRun s γ who r' ∗
      ⌜if mr.watchId = -1 ∨ (mr.canceled = true ∧ mr.cancelReason ≠ []) then
         r'.subs = r.subs ∧ r'.resuming = r.resuming ∧ r'.joined = r.joined ∧ r'.closeErr ≠ none
       else r' = { r with subs := r.subs ++ [(mr.watchId, ws)] }⌝ }}

end spec

end ClientV3
end EtcdGrove
end Perennial
