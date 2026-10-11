/-
`concurrency.stmSerializable.commit()` (`client/v3/concurrency/stm.go`). Lean-first (no Rocq counterpart); see
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
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

/-- `s.commit()` (a `*stmSerializable`), knowing etcd has reached `lo`: the transaction
`If(conflicts...).Then(puts...).Else(gets of the read keys...)`; nil if it failed (the `Else`
responses become the prefetched reads, and the gets are at the latest revision again), otherwise
its response, with `stmOutcome`; the state is stale either way. A client error aborts it (`stmRet`). -/
abbrev stmSerializable.commit.spec : Prop :=
  ∀ (lvl : w64) (p : Loc) (pfx : GoString) (st : STMSt) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ stmState lvl pfx p st ∗ etcdReached lo ∗ ⌜isoSer lvl = true⌝ }}
    (App (Val (p @!! go.GoType.PointerType stmSerializable.ty @!! go!"commit")) (Val #()))
  {{ (r : val), RET r; stmRet r fun resp : Loc => iprop(stmStale lvl pfx p ∗
      (⌜resp = null⌝ ∨ ⌜resp ≠ null⌝ ∗ stmOutcome pfx lvl lo st resp)) }}

end spec

end concurrency
end EtcdGrove
end Perennial
