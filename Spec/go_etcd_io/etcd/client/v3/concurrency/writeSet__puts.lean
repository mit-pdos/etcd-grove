/-
`concurrency.writeSet.puts()` (`client/v3/concurrency/stm.go`). Lean-first (no Rocq counterpart); see
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- `ws.puts()`: the writes' operations, in the map's order (`WriteOpsOk`), as `Op`s a transaction
runs (`txnOpOf`). -/
abbrev writeSet.puts.spec : Prop :=
  ∀ (m : Loc) (dq : DFrac) (pfx : GoString) (wsMap : GMap GoString stmPut)
    (writes : GMap GoString WriteM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ m ↦${dq} wsMap ∗ writesAt pfx wsMap writes }}
    (App (Val (m @!! writeSet.ty @!! go!"puts")) (Val #()))
  {{ (sl : GoSlice), RET #sl; m ↦${dq} wsMap ∗
      ∃ (os : List OpFull) (ops : List TxnOp), opsAt sl os ∗
        ⌜os.map txnOpOf = ops.map some ∧ WriteOpsOk writes ops⌝ }}

end spec

end concurrency
end EtcdGrove
end Perennial
