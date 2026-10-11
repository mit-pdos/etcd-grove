/-
`txnReadWrite__DeleteRange` (`kv.go`). Lean-first (no Rocq counterpart); see `InvRoTxn.lean`.

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

/-- `trw.DeleteRange(key, end)` panics (`panic("unexpected DeleteRange")`). -/
abbrev mvcc.txnReadWrite.DeleteRange.spec : Prop :=
  ∀ (trw : Loc) (key endk : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc }}
    (App (App (Val (trw @!! go.GoType.PointerType txnReadWrite.ty @!! go!"DeleteRange"))
      (Val #key)) (Val #endk))
  {{ (r : val), RET r; ⌜∃ p : val, r = PanicV p⌝ }}

end spec

end EtcdGrove
end Perennial
