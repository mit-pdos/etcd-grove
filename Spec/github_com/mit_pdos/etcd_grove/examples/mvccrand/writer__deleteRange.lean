/- Lean-first (no Rocq counterpart).

`w.deleteRange(i)` (`examples/mvccrand/mvccrand.go`, the server's `txn.DeleteRange`): a write
transaction that reads the range's previous key-values, then deletes them, every result checked (the
hook ran with the index `i`; the read, by `checkRange`; the count of keys deleted and the revision,
the pending one if any was, else the last), then `end`. As `put`, without a value drawn.
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
abbrev writer.deleteRange.spec : Prop :=
  ∀ (w : Loc) (wv : writer) (γ : RandNames) (B : BkRef) (f : GoFunc) (q : Qp) (σ : MvccState)
    (Hs : List HRev) (L : List w64) (i s : w64),
  {{ writerCtx w wv γ B f ∗ writerOwn wv γ B q σ Hs L ∗ hookPre wv i s }}
    (App (Val (w @!! go.GoType.PointerType writer.ty @!! go!"deleteRange")) (Val #i))
  {{ RET #(); (∃ (σ' : MvccState) (Hs' : List HRev), writerOwn (GF := GF) wv γ B q σ' Hs' L) ∗ hookPost wv i }}

end spec

end mvccrand
end EtcdGrove
end Perennial
