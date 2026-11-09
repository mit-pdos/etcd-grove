/-
`(*watchGRPCStream).closeSubstream(ws)`: a stopped substream: its channel to a waiting `Watch` (`retc`, unless `outc` is `nil`), then its consumer's channel ended (an error response from a goroutine, `sendCloseSubstream`, if `closeErr` is set and the watch's context not done; else closed), and forgotten. Users: `run`.
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

/-- `s.closeSubstream(ws)`. -/
def watchGRPCStream.closeSubstream.spec : Prop :=
  ∀ (s w ws : Loc) (γ : Cluster) (who : Principal) (r : RunM) (q : WsM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ wgsAt s w γ who ∗ wgsRun s γ who r ∗ wsClosed ws s γ who q }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"closeSubstream")) (Val #ws))
  {{ RET #(); ∃ r' : RunM, wgsRun s γ who r' ∗
      ⌜r'.closeErr = r.closeErr ∧ r'.joined = r.joined ∧
        (if q.id ≠ -1 then r'.subs = r.subs.filter (fun e => decide (e.1 ≠ q.id)) ∧
           r'.resuming = r.resuming
         else r'.subs = r.subs ∧
           r'.resuming = r.resuming.map (fun x => if x = ws then null else x))⌝ }}

end spec

end ClientV3
end EtcdGrove
end Perennial
