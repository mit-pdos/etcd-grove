/-
**Laws of the API's vocabulary** (mvccfull's Probe, 2026-11-09, the unfold list): what a client of
`Restore` and of the lessor's range deleter used to get by unfolding `hookRun` and `mvccDeleter`. In
a module of its own, so that adding them leaves `Api` (and its importers) as they were.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **With no hook, the hook's run is the caller's view shift.** -/
theorem hookRun_nil (P Pre Q : IProp GF) :
    hookRun P func.nil Pre Q ⊣⊢ iprop(P ∗ Pre ={⊤}=∗ Q) := by
  unfold hookRun; simp only [↓reduceIte]; exact .rfl

instance mvccDeleter_persistent (rd : GoFunc) (γ : MvccName) :
    Persistent (mvccDeleter (GF := GF) rd γ) := by
  unfold mvccDeleter; infer_instance

/-- **A range deleter from its triple**: `rd`, not `nil`, writes as the store's `Write` does. -/
theorem mvccDeleter_intro (rd : GoFunc) (γ : MvccName) :
    iprop(⌜rd ≠ func.nil⌝ ∗ □ ∀ (q : Qp) (B : MvccStorage) (P Pre Q : IProp GF) (f : GoFunc)
        (R : MvccState → IProp GF),
      {{ mvccReaders γ 1 ∗ mvccBackend γ q B P ∗ hookIs B f ∗ Pre ∗ hookRun P f Pre Q ∗
          AU <{ ∃∃ (σ : MvccState), mvccState γ σ }> @ ⊤ \ ↑mvccN, ∅
            <{ ⌜σ.pending = none⌝ ∗ mvccState γ σ, COMM R σ }> }}
        (App (Val #rd) (Val #()))
      {{ (t : GoInterface), RET #t; mvccBackend γ q B P ∗
          (∃ (trace : Loc) (σ : MvccState), mvccTxn t γ trace (.write σ []) ∗ R σ) ∗ Q }}) ⊢
    mvccDeleter rd γ := by
  unfold mvccDeleter; exact .rfl

end laws

end api
end mvcc
end EtcdGrove
end Perennial
