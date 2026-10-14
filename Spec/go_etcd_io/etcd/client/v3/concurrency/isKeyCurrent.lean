/-
`concurrency.isKeyCurrent(k, r)` (`client/v3/concurrency/stm.go`). Lean-first (no Rocq counterpart); see
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

/-- `isKeyCurrent(k, r)` for the read `e` of `k`: `ModRevision(k) = ` its mod revision (`readCmp`). -/
abbrev isKeyCurrent.spec : Prop :=
  ∀ (pfx k : GoString) (p : Loc) (e : ReadM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ readRespAt pfx k p e }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.concurrency.isKeyCurrent)) (Val #k)) (Val #p))
  {{ (c : go_etcd_io.etcd.client.v3.Cmp), RET #c; cmpAt c (readCmp k e) }}

end spec

end concurrency
end EtcdGrove
end Perennial
