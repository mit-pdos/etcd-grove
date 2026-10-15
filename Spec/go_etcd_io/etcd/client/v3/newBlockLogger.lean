/-
`clientv3.newBlockLogger(interval, threshold, now, logFunc)` (`client/v3/block_logger.go`; the watch slice's unit W-C). Lean-first (no Rocq counterpart).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- `newBlockLogger(interval, threshold, now, logFunc)` with `now` nil or returning a time, and a
`logFunc` that keeps `A x` for every `x`: a block logger (`isBlockLogger`). -/
abbrev newBlockLogger.spec : Prop :=
  ∀ (α : Type) (A : α → IProp GF) (iv th : _root_.Perennial.time.Duration) (nowf lf : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      (⌜nowf = func.nil⌝ ∨ □ ∀ Φ : val → IProp GF, ▷ (∀ t : _root_.Perennial.time.Time, Φ #t) -∗
        WP (App (Val #nowf) (Val #())) {{ Φ }}) ∗
      (□ ∀ (x : α) (n : w64) (d1 d2 : _root_.Perennial.time.Duration),
        {{ A x }} (App (App (App (Val #lf) (Val #n)) (Val #d1)) (Val #d2)) {{ RET #(); A x }}) }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.client.v3.newBlockLogger)) (Val #iv)) (Val #th))
      (Val #nowf)) (Val #lf))
  {{ (bl : Loc), RET #bl; isBlockLogger bl A }}

end spec

end EtcdGrove
end Perennial
