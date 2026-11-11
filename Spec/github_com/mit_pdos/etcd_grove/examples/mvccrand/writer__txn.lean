/- Lean-first (no Rocq counterpart).

`w.txn(i)` (`examples/mvccrand/mvccrand.go`, the server's `txn.Txn`): a read transaction (either
mode) at exactly the writer's revision, checked (`Rev`, `FirstRev() == -1`, a range by
`checkRange`), then either a read-only transaction made of it (one to three ranges checked, no
change, `End`), or, ended, a write transaction at the read's revision (the hook ran with the index
`i`; one to three `writeOp`s; its changes non-empty iff the model's) and `end`. The writer, between
operations (`writerOwn`), ends between operations; the hook saved `i` if the transaction wrote
(`hookPost`), else nothing ran (`hookPre`, unchanged); at most three values drawn (`vals`).
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
abbrev writer.txn.spec : Prop :=
  ∀ (w : Loc) (wv : writer) (γ : RandNames) (B : MvccStorage) (f : GoFunc) (q : Qp) (σ : MvccState)
    (Hs : List HRev) (L : List w64) (i s n : w64),
  0 ≤ sint.Z n → sint.Z n + 3 < 2 ^ 63 →
  {{ writerCtx w wv γ B f ∗ writerOwn wv γ B q σ Hs L ∗ hookPre wv i s ∗ wF go!"vals" w ↦ n }}
    (App (Val (w @!! go.GoType.PointerType writer.ty @!! go!"txn")) (Val #i))
  {{ RET #(); (∃ (σ' : MvccState) (Hs' : List HRev), writerOwn (GF := GF) wv γ B q σ' Hs' L) ∗
      (hookPost wv i ∨ hookPre wv i s) ∗
      ∃ n' : w64, wF go!"vals" w ↦ n' ∗ ⌜sint.Z n ≤ sint.Z n' ∧ sint.Z n' ≤ sint.Z n + 3⌝ }}

end spec

end mvccrand
end EtcdGrove
end Perennial
