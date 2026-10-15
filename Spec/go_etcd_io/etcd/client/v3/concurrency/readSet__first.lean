/-
`concurrency.readSet.first()` (`client/v3/concurrency/stm.go`). Lean-first (no Rocq counterpart); see
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

/-- `rs.first()`: the least header revision of the reads (`FirstOk`). -/
abbrev readSet.first.spec : Prop :=
  ∀ (m : Loc) (dq : DFrac) (pfx : GoString) (rsMap : GMap GoString Loc)
    (reads : GMap GoString ReadM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.concurrency ∗ m ↦${dq} rsMap ∗ readsAt pfx rsMap reads }}
    (App (Val (m @!! readSet.ty @!! go!"first")) (Val #()))
  {{ (f : w64), RET #f; m ↦${dq} rsMap ∗ ⌜FirstOk reads f⌝ }}

end spec

end concurrency
end EtcdGrove
end Perennial
