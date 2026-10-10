/-
`concurrency.stm.Get(keys...)` (`client/v3/concurrency/stm.go`). Lean-first (no Rocq counterpart); see
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

/-- `s.Get(keys...)` (a `*stm`: `RepeatableReads`, `ReadCommitted`), keys under `pfx`: a written
key's value, or `fetch`'s (`GetPost`). A client error aborts it (`stmPanic.spec`). -/
abbrev stm.Get.spec : Prop :=
  ∀ (b : Loc) (pfx : GoString) (st : STMSt) (gs : List (OpFull → OpFull)) (ksl : GoSlice)
    (ks : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ stmEnv pfx b ∗ stmRsetOwn pfx b st.reads ∗ stmWsetOwn pfx b st.writes ∗
      stmOptsOwn b gs ∗ ⌜ReadOptsOk gs⌝ ∗ ksl ↦*□ ks ∗ ⌜∀ k ∈ ks, pfx <+: k⌝ }}
    (App (Val (b @!! go.GoType.PointerType stm.ty @!! go!"Get")) (Val #ksl))
  {{ (v : GoString), RET #v; ∃ reads' : GMap GoString ReadM, stmRsetOwn pfx b reads' ∗
      stmWsetOwn pfx b st.writes ∗ stmOptsOwn b gs ∗
      ⌜GetPost ks st v { reads := reads', writes := st.writes }⌝ }}

end spec

end concurrency
end EtcdGrove
end Perennial
