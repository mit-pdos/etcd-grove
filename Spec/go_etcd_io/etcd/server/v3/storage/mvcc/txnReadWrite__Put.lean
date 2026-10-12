/-
`txnReadWrite__Put` (`kv.go`). Lean-first (no Rocq counterpart); see `InvRoTxn.lean`.

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

/-- `trw.Put(...)` panics (`panic("unexpected Put")`), with no deferred function to recover it:
the call gets stuck where the panic reaches `exceptionDo` (`wp_exceptionDo_panic`). As for
Perennial's `shouldPanic`, the spec states where it gets stuck, assuming a WP of that
expression (which only `▷ False` provides). -/
abbrev mvcc.txnReadWrite.Put.spec : Prop :=
  ∀ (trw : Loc) (key value : GoSlice) (lease : w64) (Φ : val → IProp GF),
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      (∀ Ψ : val → IProp GF,
        WP (App (Val exceptionDo)
          (Val (panicVal #(interface.mkOk go.string #(go!"unexpected Put"))))) {{ Ψ }}) ⊢
      WP (App (App (App (Val (trw @!! go.GoType.PointerType txnReadWrite.ty @!! go!"Put")) (Val #key))
        (Val #value)) (Val #lease)) {{ Φ }}

end spec

end EtcdGrove
end Perennial
