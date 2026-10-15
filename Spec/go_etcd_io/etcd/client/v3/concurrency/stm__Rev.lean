/-
`concurrency.stm.Rev(key)` (`client/v3/concurrency/stm.go`). Lean-first (no Rocq counterpart); see
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

/-- `s.Rev(k)`: `fetch(k)`'s mod revision of `k` (`0`: absent); the reads grow by `k` and hold
it. A client error aborts it (`stmRet`). -/
abbrev stm.Rev.spec : Prop :=
  ∀ (b : Loc) (pfx : GoString) (reads : GMap GoString ReadM) (gs : List (OpFull → OpFull))
    (k : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ stmEnv pfx b ∗ stmRsetOwn pfx b reads ∗ stmOptsOwn b gs ∗ ⌜ReadOptsOk gs⌝ ∗
      ⌜pfx <+: k⌝ }}
    (App (Val (b @!! go.GoType.PointerType stm.ty @!! go!"Rev")) (Val #k))
  {{ (r : val), RET r; stmRet r fun rev : w64 => iprop(
      ∃ reads' : GMap GoString ReadM, stmRsetOwn pfx b reads' ∗
      stmOptsOwn b gs ∗ ⌜ReadsGrow reads reads' [k] ∧ ∃ e, reads' !! k = some e ∧ rev = e.modRev⌝) }}

end spec

end concurrency
end EtcdGrove
end Perennial
