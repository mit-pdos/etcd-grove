/-
`concurrency.stm.commit()` (`client/v3/concurrency/stm.go`). Lean-first (no Rocq counterpart); see
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

/-- `s.commit()` (a `*stm`; any level's conflicts closure), knowing etcd has reached `lo`: the
transaction `If(conflicts...).Then(puts...)`; nil if it failed, otherwise its response, with
`stmOutcome`. A client error aborts it (`stmRet`). -/
abbrev stm.commit.spec : Prop :=
  ∀ (lvl : w64) (b : Loc) (pfx : GoString) (st : STMSt) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ stmEnv pfx b ∗ stmRsetOwn pfx b st.reads ∗ stmWsetOwn pfx b st.writes ∗
      stmConflictsAt lvl pfx b ∗ etcdReached lo }}
    (App (Val (b @!! go.GoType.PointerType stm.ty @!! go!"commit")) (Val #()))
  {{ (r : val), RET r; stmRet r fun resp : Loc => iprop(
      stmRsetOwn pfx b st.reads ∗ stmWsetOwn pfx b st.writes ∗
      (⌜resp = null⌝ ∨ ⌜resp ≠ null⌝ ∗ stmOutcome pfx lvl lo st resp)) }}

end spec

end concurrency
end EtcdGrove
end Perennial
