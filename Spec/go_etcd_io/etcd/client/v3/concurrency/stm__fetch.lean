/-
`concurrency.stm.fetch(keys...)` (`client/v3/concurrency/stm.go`). Lean-first (no Rocq counterpart); see
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

/-- `s.fetch(keys...)`, keys under `pfx`: nil for no key; the read of the first key already read,
if any; otherwise one read transaction getting every key (with the get options), whose
responses are added to the reads, and the first key's. The read returned may differ from the read set's entry of its key in its
header revision (not in its key-value): with a key listed twice, the read set keeps the later
response (`readsAdd`), and the range responses of one transaction are not modelled to share a
header. A client error aborts it (`stmRet`). -/
abbrev stm.fetch.spec : Prop :=
  ∀ (b : Loc) (pfx : GoString) (reads : GMap GoString ReadM) (gs : List (OpFull → OpFull))
    (ksl : GoSlice) (ks : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ stmEnv pfx b ∗ stmRsetOwn pfx b reads ∗ stmOptsOwn b gs ∗ ⌜ReadOptsOk gs⌝ ∗
      ksl ↦*□ ks ∗ ⌜∀ k ∈ ks, pfx <+: k⌝ }}
    (App (Val (b @!! go.GoType.PointerType stm.ty @!! go!"fetch")) (Val #ksl))
  {{ (r : val), RET r; stmRet r fun p : Loc => iprop(
      ∃ reads' : GMap GoString ReadM, stmRsetOwn pfx b reads' ∗
      stmOptsOwn b gs ∗ ⌜ReadsGrow reads reads' ks⌝ ∗
      (⌜ks = [] ∧ p = null⌝ ∨
        ∃ (k : GoString) (e e' : ReadM), ⌜k ∈ ks ∧ reads' !! k = some e' ∧ e'.kv = e.kv⌝ ∗
          readRespAt pfx k p e)) }}

end spec

end concurrency
end EtcdGrove
end Perennial
