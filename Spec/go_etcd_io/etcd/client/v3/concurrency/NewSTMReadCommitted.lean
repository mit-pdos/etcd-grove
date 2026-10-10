/-
`concurrency.NewSTMReadCommitted(ctx, c, apply)` (`client/v3/concurrency/stm.go`, deprecated). Lean-first (no Rocq counterpart); see
`InvSTM.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.concurrency.InvSTM

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- `NewSTMReadCommitted(ctx, c, apply)`: `NewSTM(c, apply, WithAbortContext(ctx), WithIsolation(ReadCommitted))`. -/
abbrev NewSTMReadCommitted.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cs : context.ContextDesc (IProp GF)) (c : Loc) (pfx : GoString)
    (apply : GoFunc) (Q : STMSt → Prop) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ context.isContext ctx cs ∗ isEtcdSTMClient c pfx ∗ applySpec pfx apply Q ∗
      etcdReached lo }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.NewSTMReadCommitted)) (Val #(GoInterface.ok ctx)))
      (Val #c)) (Val #apply))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); stmResult pfx isoRC lo Q resp err }}

end spec

end concurrency
end EtcdGrove
end Perennial
