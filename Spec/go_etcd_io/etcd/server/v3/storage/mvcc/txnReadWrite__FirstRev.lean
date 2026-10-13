/-
`txnReadWrite__FirstRev` (`kv.go`). Lean-first (no Rocq counterpart); see `InvRoTxn.lean`.

-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvRoTxn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `trw.FirstRev()`: the read transaction's first revision, the compaction revision `crev` it
observed (2026-10-13, unit 6a; `-1` of the frozen transaction, the instance at `isRoTxnWrite`'s
defaults). -/
abbrev mvcc.txnReadWrite.FirstRev.spec : Prop :=
  ∀ (trw s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64) (crev : Int) (Z : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.isRoTxnWrite trw s γ log rev crev Z }}
    (App (Val (trw @!! go.GoType.PointerType txnReadWrite.ty @!! go!"FirstRev")) (Val #()))
  {{ RET #(W64 crev); mvcc.isRoTxnWrite trw s γ log rev crev Z }}

end spec

end EtcdGrove
end Perennial
