/- Lean-first (no Rocq counterpart).

`w.read()` (`examples/mvccrand/mvccrand.go`): the writer's own read, between transactions
(`writerOwn`): a read transaction at exactly its revision (it is the only writer), checked
(`tr.Rev() == cur`, then `checkRange` of a random range against its history's snapshot). Every
check passes; the writer's state is unchanged (its generator moves).
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
abbrev writer.read.spec : Prop :=
  ∀ (w : Loc) (wv : writer) (γ : RandNames) (B : BkRef) (f : GoFunc) (q : Qp) (σ : MvccState)
    (Hs : List HRev) (L : List w64),
  {{ writerCtx w wv γ B f ∗ writerOwn wv γ B q σ Hs L }}
    (App (Val (w @!! go.GoType.PointerType writer.ty @!! go!"read")) (Val #()))
  {{ RET #(); writerOwn (GF := GF) wv γ B q σ Hs L }}

end spec

end mvccrand
end EtcdGrove
end Perennial
