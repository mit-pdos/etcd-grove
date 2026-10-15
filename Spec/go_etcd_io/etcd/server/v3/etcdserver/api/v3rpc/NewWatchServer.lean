/-
`v3rpc.NewWatchServer` (`watch.go`). Lean-first (no Rocq counterpart); the vocabulary is
`v3rpc/InvWatch.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`NewWatchServer(s)`** on the server `s` whose KV is the watchable store `wsl` (`s.kv`, and
the server's contract for the watch path, `watchSrvOk`), whose ids are readable (`srvIdsOk`), with
its configuration's logger and request budget (read-only) and its progress interval (owned: the
constructor raises it to `100ms` if it is below; at most `2 ^ 62` nanoseconds, the interval's
lock invariant): a `WatchServer` holding a `*watchServer` (`isWatchServer`), the interval back. -/
abbrev v3rpc.NewWatchServer.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γ : mvcc.WsNames) (wsl lg0 : Loc) (m d : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.watchSrvOk s E γ wsl ∗ srvKVAddr s ↦□ v3rpc.wsIface wsl ∗ v3rpc.srvIdsOk s ∗
      srvCfgFieldAddr s go!"Logger" ↦□ lg0 ∗ srvCfgFieldAddr s go!"MaxRequestBytes" ↦□ m ∗
      srvCfgFieldAddr s go!"WatchProgressNotifyInterval" ↦ d ∗ ⌜sint.Z d ≤ 2 ^ 62⌝ }}
    (App (Val (@! v3rpc.NewWatchServer)) (Val #s))
  {{ (ws : GoInterface), RET #ws; ∃ (p lg : Loc) (cid mid d' : w64),
      ⌜ws = interface.mkOk (go.GoType.PointerType v3rpc.watchServer.ty) #p⌝ ∗
      v3rpc.isWatchServer p ⟨s, E, wsl, γ, cid, mid, lg, m + W64 (512 * 1024)⟩ ∗
      srvCfgFieldAddr s go!"WatchProgressNotifyInterval" ↦ d' }}

end spec

end EtcdGrove
end Perennial
