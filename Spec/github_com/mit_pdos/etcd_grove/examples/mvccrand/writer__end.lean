/- Lean-first (no Rocq counterpart).

`w.end(p, end)` (`examples/mvccrand/mvccrand.go`): the writer ends its transaction (begun at the
store's state `σ`, the history at `Hs`, mvcc's pending changes `pend`, their model `P` at `p`,
`pendOk`): it appends the pending revision to the history if it has a change (`histAfter`), runs
`end` (`endCb`: the store's `End`, which commits `pend`; `E`, `E'` the caller's), checks the store's
revision and publishes it. After it the writer is between transactions at the committed state
(`commitSt σ pend`) and the new history, the thread token back.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.Writer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc mvcc.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- See the file header. -/
abbrev writer.end.spec : Prop :=
  ∀ (w : Loc) (wv : writer) (γ : RandNames) (σ : MvccState) (Hs : List HRev) (p : Loc) (P : PendM)
    (pend : List Change) (e : GoFunc) (E E' : IProp GF),
  pendOk σ Hs pend P →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      writerRO w wv ∗ histRd wv.h' γ.h ∗ inv worldN (worldInv wv.h' γ) ∗ isMvcc wv.kv' γ.kv ∗
      writerIdle γ σ Hs ∗ ownPending p P ∗ endCb e γ σ pend (histAfter Hs P) E E' ∗ E }}
    (App (App (Val (w @!! go.GoType.PointerType writer.ty @!! go!"end")) (Val #p)) (Val #e))
  {{ RET #(); histRd wv.h' γ.h ∗ threadTok ∗ E' ∗
      writerIdle γ (commitSt σ pend) (histAfter Hs P) }}

end spec

end mvccrand
end EtcdGrove
end Perennial
