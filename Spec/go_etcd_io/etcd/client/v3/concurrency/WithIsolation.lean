/-
`concurrency.WithIsolation(lvl)` (`client/v3/concurrency/stm.go`). Lean-first (no Rocq counterpart); see
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

/-- `WithIsolation(lvl)`: an option setting the isolation level. -/
abbrev WithIsolation.spec : Prop :=
  ∀ (lvl : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency }}
    (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.WithIsolation)) (Val #lvl))
  {{ (f : GoFunc), RET #f; stmOptSpec f (withIsoM lvl) }}

end spec

end concurrency
end EtcdGrove
end Perennial
