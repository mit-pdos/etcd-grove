/-
`concurrency.writeSet.cmps(rev)` (`client/v3/concurrency/stm.go`). Lean-first (no Rocq counterpart); see
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

/-- `ws.cmps(rev)`: one comparison `ModRevision(k) < rev` per written key (`WriteCmpsOk`).
 -/
abbrev writeSet.cmps.spec : Prop :=
  ∀ (m : Loc) (dq : DFrac) (pfx : GoString) (wsMap : GMap GoString stmPut)
    (writes : GMap GoString WriteM) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ m ↦${dq} wsMap ∗ writesAt pfx wsMap writes }}
    (App (Val (m @!! writeSet.ty @!! go!"cmps")) (Val #rev))
  {{ (sl : GoSlice), RET #sl; m ↦${dq} wsMap ∗
      ∃ ms : List CmpModel, cmpsAt sl ms ∗ ⌜WriteCmpsOk writes rev ms⌝ }}

end spec

end concurrency
end EtcdGrove
end Perennial
