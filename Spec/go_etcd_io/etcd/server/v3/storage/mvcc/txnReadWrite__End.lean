/-
`txnReadWrite__End` (`kv.go`). Lean-first (no Rocq counterpart); see `InvRoTxn.lean`.

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

/-- `trw.End()`: the read transaction ended (`metricsTxnWrite.End`): its tokens back
(`storeReaderC`, with the reader's tag `Z`; 2026-10-13, unit 6a). The readers' statement
(`storeReader`) is `specR` (`spec_R`, `ReaderSpecs.lean`). -/
abbrev mvcc.txnReadWrite.End.spec : Prop :=
  ∀ (trace : Loc) (trw s : Loc) (γ : mvcc.StoreNames) (log : mvcc.Log) (rev : w64) (crev : Int)
    (Z : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.isRoTxnWrite trw s γ trace log rev crev Z }}
    (App (Val (trw @!! go.GoType.PointerType txnReadWrite.ty @!! go!"End")) (Val #()))
  {{ RET #(); mvcc.storeReaderC s γ ∗ □ Z ∗ (∃ te : Bool, traceutil.ownTrace trace te) }}

/-- **Candidate** (2026-11-01, `notes/mvcc-api-candidate.md`; over `Api.lean`, not proved). `t.End()`: the read transaction ended; the caller's thread token and trace its own. -/
abbrev mvcc.txnReadWrite.End.specC : Prop :=
  ∀ (trw : Loc) (γ : mvcc.MvccName) (trace : Loc) (σ : mvcc.MvccState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.mvccRoTxn trw γ trace σ }}
    (App (Val (trw @!! go.GoType.PointerType txnReadWrite.ty @!! go!"End")) (Val #()))
  {{ RET #(); threadTok ∗ (∃ te : Bool, traceutil.ownTrace trace te) }}

end spec

end EtcdGrove
end Perennial
