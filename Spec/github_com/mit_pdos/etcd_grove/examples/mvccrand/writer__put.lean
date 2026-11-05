/- Lean-first (no Rocq counterpart).

`w.put(i)` (`examples/mvccrand/mvccrand.go`, the server's `txn.Put`): a write transaction that reads
the key's previous key-value, then puts a new value (with no lease or a live one), every result
checked (the hook ran with the index `i` being applied; the transaction's revision; the read, by
`checkRange`; the put's revision), then `end`. The writer, between operations (`writerOwn`), ends
between operations at the committed state and history; the hook saved `i` (`hookPre` to `hookPost`);
one value drawn (`vals`).
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
abbrev writer.put.spec : Prop :=
  ∀ (w : Loc) (wv : writer) (γ : RandNames) (B : BkRef) (f : GoFunc) (q : Qp) (σ : MvccState)
    (Hs : List HRev) (L : List w64) (i s n : w64),
  0 ≤ sint.Z n → sint.Z n + 1 < 2 ^ 63 →
  {{ writerCtx w wv γ B f ∗ writerOwn wv γ B q σ Hs L ∗ hookPre wv i s ∗ wF go!"vals" w ↦ n }}
    (App (Val (w @!! go.GoType.PointerType writer.ty @!! go!"put")) (Val #i))
  {{ RET #(); (∃ (σ' : MvccState) (Hs' : List HRev), writerOwn (GF := GF) wv γ B q σ' Hs' L) ∗ hookPost wv i ∗
      wF go!"vals" w ↦ (n + W64 1) }}

end spec

end mvccrand
end EtcdGrove
end Perennial
