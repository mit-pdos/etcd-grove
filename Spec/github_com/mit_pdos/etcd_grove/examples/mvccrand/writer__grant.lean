/- Lean-first (no Rocq counterpart).

`w.grant(i)` (`examples/mvccrand/mvccrand.go`): the writer, between operations (`writerOwn`, its
lessor's resources `writerLe`, `WriterLease.lean`), applying index `i` (the hook's counters,
`hookPre`), grants the lease `nextID + 1` (its id never live, not `0`, its TTL below the maximum:
`Grant` returns `nil`, the check), under the batch lock, the hook running with `i` (`checkHook`), one
write token spent; the model records it, and the store's revision is the published one (the check:
a grant makes no revision). After it the writer is between operations again with the lease live
(`L ++ [n + 1]`, the model's map too), the hook's counters at `i` (`hookPost`).
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
abbrev writer.grant.spec : Prop :=
  ∀ (w : Loc) (wv : writer) (γ : RandNames) (B : mvcc.KBReal) (f : GoFunc) (q : Qp) (σ : MvccState)
    (Hs : List HRev) (L : List w64) (n : w64) (k : Nat) (T R : IProp GF) (i s : w64),
  0 < k → sint.Z n + 1 < 2 ^ 63 →
  {{ writerCtx w wv γ (etcdStorage B) f ∗ writerOwn wv γ (etcdStorage B) q σ Hs L ∗ writerLe w wv γ B f L n k T R ∗
      hookPre wv i s }}
    (App (Val (w @!! go.GoType.PointerType writer.ty @!! go!"grant")) (Val #i))
  {{ RET #(); writerOwn wv γ (etcdStorage B) q σ Hs (L ++ [n + W64 1]) ∗
      writerLe w wv γ B f (L ++ [n + W64 1]) (n + W64 1) (k - 1) T R ∗ hookPost wv i }}

end spec

end mvccrand
end EtcdGrove
end Perennial
