/-
`txnReadWrite__Rev` (`kv.go`). Lean-first (no Rocq counterpart); see `InvRoTxn.lean`.

-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvRoTxn
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `trw.Rev()`: the read transaction's revision, the last of its committed log. -/
abbrev mvcc.txnReadWrite.Rev.spec : Prop :=
  ∀ (trace : Loc) (trw s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64) (crev : Int)
    (Z : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.isRoTxnWrite trw s γ trace log rev crev Z }}
    (App (Val (trw @!! go.GoType.PointerType txnReadWrite.ty @!! go!"Rev")) (Val #()))
  {{ RET #rev; mvcc.isRoTxnWrite trw s γ trace log rev crev Z ∗
      ⌜log ≠ [] ∧ rev = W64 ((log.length : Int) - 1)⌝ }}

/-- **Candidate** (round 8, 2026-11-02, `notes/mvcc-api-candidate.md`; over `Api.lean`, not proved). `t.Rev()`: the read transaction's revision. -/
abbrev mvcc.txnReadWrite.Rev.specC : Prop :=
  ∀ (trw : Loc) (γ : mvcc.MvccName) (trace : Loc) (σ : mvcc.MvccState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.mvccTxn (interface.mkOk (go.GoType.PointerType txnReadWrite.ty) #trw) γ trace (.read σ) }}
    (App (Val (trw @!! go.GoType.PointerType txnReadWrite.ty @!! go!"Rev")) (Val #()))
  {{ RET #(W64 (σ.rev : Int) : w64); mvcc.mvccTxn (interface.mkOk (go.GoType.PointerType txnReadWrite.ty) #trw) γ trace (.read σ) }}

end spec

end EtcdGrove
end Perennial
