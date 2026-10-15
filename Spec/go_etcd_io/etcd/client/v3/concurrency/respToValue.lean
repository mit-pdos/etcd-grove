/-
`concurrency.respToValue(resp)` (`client/v3/concurrency/stm.go`). Lean-first (no Rocq counterpart); see
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

/-- `respToValue(resp)`: `""` for nil, otherwise the read's value. -/
abbrev respToValue.spec : Prop :=
  ∀ (p : Loc) (v : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ (⌜p = null ∧ v = []⌝ ∨
      ∃ (pfx k : GoString) (e : ReadM), readRespAt pfx k p e ∗ ⌜v = e.value⌝) }}
    (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.respToValue)) (Val #p))
  {{ RET #v; True }}

end spec

end concurrency
end EtcdGrove
end Perennial
