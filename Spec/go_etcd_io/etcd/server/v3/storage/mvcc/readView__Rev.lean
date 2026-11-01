/-
`readView__Rev` (metrics_txn.go / kv_view.go). Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
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

/-- `rv.Rev()`: a read transaction opened and closed; the last revision of a committed log. Of
a store that may be compacted (`storeReaderC`; 2026-10-13, unit 6a); the readers' statement
(`storeReader`) is `specR` (`spec_R`, `ReaderSpecs.lean`). -/
abbrev mvcc.readView.Rev.spec : Prop :=
  ∀ (rv s : Loc) (γ : mvcc.StoreNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isReadView rv s γ ∗ mvcc.storeReaderC s γ }}
    (App (Val (rv @!! go.GoType.PointerType readView.ty @!! go!"Rev")) (Val #()))
  {{ (v : w64), RET #v; mvcc.storeReaderC s γ ∗
      ∃ log : mvcc.Log, mvcc.idxCert γ.idx log ∗ ⌜log ≠ [] ∧ v = W64 ((log.length : Int) - 1)⌝ }}

/-- **Candidate** (2026-11-01, `notes/mvcc-api-candidate.md`; over `Api.lean`, not proved). `rv.Rev()` (the store's `Rev`): the current revision, the caller's update fired at the
state, unchanged. -/
abbrev mvcc.readView.Rev.specC : Prop :=
  ∀ (rv : Loc) (γ : mvcc.MvccName) (Q : mvcc.MvccState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ mvcc.isReadViewOf rv γ ∗ threadTok ∗
      AU <{ ∃∃ (σ : mvcc.MvccState), mvcc.mvccState γ σ }> @ ⊤ \ ↑mvcc.mvccN, ∅
        <{ mvcc.mvccState γ σ, COMM Q σ }> }}
    (App (Val (rv @!! go.GoType.PointerType readView.ty @!! go!"Rev")) (Val #()))
  {{ (v : w64), RET #v; threadTok ∗ ∃ σ : mvcc.MvccState, Q σ ∗ ⌜v = W64 (σ.rev : Int)⌝ }}

end spec

end EtcdGrove
end Perennial
