/- Lean-first (no Rocq counterpart).

`w.checkLeases()` (`examples/mvccrand/mvccrand.go`): the writer, between operations (`writerOwn`,
`writerLe`, `WriterLease.lean`), checks the lessor's record of the keys on each lease against the
model's last state (the snapshot's last map, the store's state after its log, `stMatch`): each key's
lease (`GetLease`, the lease owner's item map, which is the store's state's `leaseItemsOf`) is the
model's (`0` for none), and each of the model's live leases is the lessor's (`Lookup` not `nil`: the
live set is `L`) with exactly the model's keys on it (`Keys()`, sorted, against the tester's keys in
order). Every check passes, and nothing changes.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.WriterLease

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
abbrev writer.checkLeases.spec : Prop :=
  ∀ (w : Loc) (wv : writer) (γ : RandNames) (B : mvcc.KBReal) (f : GoFunc) (q : Qp) (σ : MvccState)
    (Hs : List HRev) (L : List w64) (n : w64) (k : Nat) (T R : IProp GF),
  {{ writerCtx w wv γ (etcdStorage B) f ∗ writerOwn wv γ (etcdStorage B) q σ Hs L ∗ writerLe w wv γ B f L n k T R }}
    (App (Val (w @!! go.GoType.PointerType writer.ty @!! go!"checkLeases")) (Val #()))
  {{ RET #(); writerOwn wv γ (etcdStorage B) q σ Hs L ∗ writerLe w wv γ B f L n k T R }}

end spec

end mvccrand
end EtcdGrove
end Perennial
