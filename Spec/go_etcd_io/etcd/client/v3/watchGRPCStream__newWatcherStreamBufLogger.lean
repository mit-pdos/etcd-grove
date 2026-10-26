/-
`(*clientv3.watchGRPCStream).newWatcherStreamBufLogger(ws, now)` (`client/v3/watch.go`; (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- `w.newWatcherStreamBufLogger(ws, now)` (a non-nil logger, `now` returning a time): a block
logger whose log function reads the request's key, range end and revision and the buffer's
length (`wsLogA`) and logs them. -/
abbrev watchGRPCStream.newWatcherStreamBufLogger.spec : Prop :=
  ∀ (wgs ws lg : Loc) (key ed : GoString) (nowf : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ wgsF wgs go!"lg" ↦□ lg ∗
      ⌜lg ≠ null⌝ ∗ wsReqF ws go!"key" ↦□ key ∗ wsReqF ws go!"end" ↦□ ed ∗
      (□ ∀ Φ : val → IProp GF, ▷ (∀ t : _root_.Perennial.time.Time, Φ #t) -∗
        WP (App (Val #nowf) (Val #())) {{ Φ }}) }}
    (App (App (Val (wgs @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"newWatcherStreamBufLogger")) (Val #ws)) (Val #nowf))
  {{ (bl : Loc), RET #bl; isBlockLogger bl (wsLogA ws) }}

end spec

end EtcdGrove
end Perennial
