/- Lean-first (no Rocq counterpart).

`w.begin()` (`examples/mvccrand/mvccrand.go`): the writer, between transactions (`writerIdle`,
`World.lean`), starts the model of its next transaction: the revision after the history's last
(its published one, the check), a copy of the last revision's state, no changes.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.Writer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- See the file header. -/
abbrev writer.begin.spec : Prop :=
  ∀ (w : Loc) (wv : writer) (γ : RandNames) (σ : MvccState) (Hs : List HRev),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand ∗
      writerRO w wv ∗ histRd wv.h' γ.h ∗ inv worldN (worldInv wv.h' γ) ∗ writerIdle γ σ Hs }}
    (App (Val (w @!! go.GoType.PointerType writer.ty @!! go!"begin")) (Val #()))
  {{ (p : Loc), RET #p; histRd wv.h' γ.h ∗ writerIdle γ σ Hs ∗
      ownPending p ⟨W64 (Hs.length : Int), lastSt Hs, []⟩ }}

end spec

end mvccrand
end EtcdGrove
end Perennial
