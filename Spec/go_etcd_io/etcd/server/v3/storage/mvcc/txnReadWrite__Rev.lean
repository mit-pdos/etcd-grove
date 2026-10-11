/-
`txnReadWrite__Rev` (`kv.go`). Lean-first (no Rocq counterpart); see `InvRoTxn.lean`.

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

/-- `trw.Rev()`: the read transaction's revision, the last of its committed log. -/
abbrev mvcc.txnReadWrite.Rev.spec : Prop :=
  ∀ (trw s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.isRoTxnWrite trw s γ log rev }}
    (App (Val (trw @!! go.GoType.PointerType txnReadWrite.ty @!! go!"Rev")) (Val #()))
  {{ RET #rev; mvcc.isRoTxnWrite trw s γ log rev ∗
      ⌜log ≠ [] ∧ rev = W64 ((log.length : Int) - 1)⌝ }}

end spec

end EtcdGrove
end Perennial
