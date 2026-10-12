/-
`concurrency.stmSerializable.Get(keys...)` (`client/v3/concurrency/stm.go`). Lean-first (no Rocq counterpart); see
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

/-- `s.Get(keys...)` (a `*stmSerializable`: the serializable levels), keys under `pfx`: `""` for no
key; a written key's value; otherwise the prefetched reads of `keys` move to the read set, and
`fetch`'s value; after the attempt's first read, the gets are at its header's revision
(`WithRev`) (`GetPost`). A client error aborts it (`stmRet`). -/
abbrev stmSerializable.Get.spec : Prop :=
  ∀ (lvl : w64) (p : Loc) (pfx : GoString) (st : STMSt) (ksl : GoSlice) (ks : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ stmState lvl pfx p st ∗ ksl ↦*□ ks ∗ ⌜isoSer lvl = true ∧ ∀ k ∈ ks, pfx <+: k⌝ }}
    (App (Val (p @!! go.GoType.PointerType stmSerializable.ty @!! go!"Get")) (Val #ksl))
  {{ (r : val), RET r; stmRet r fun v : GoString => iprop(
      ∃ st' : STMSt, stmState lvl pfx p st' ∗ ⌜GetPost ks st v st'⌝) }}

end spec

end concurrency
end EtcdGrove
end Perennial
