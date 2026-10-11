/-
`storeTxnCommon__Rev` (kvstore_txn.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `tr.Rev()` is the field. -/
abbrev mvcc.storeTxnCommon.Rev.spec : Prop :=
  ∀ (tc : Loc) (v : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      tc.[storeTxnCommon, go!"rev"] ↦□ v }}
    (App (Val (tc @!! go.GoType.PointerType storeTxnCommon.ty @!! go!"Rev")) (Val #()))
  {{ RET #v; True }}

end spec

end EtcdGrove
end Perennial
