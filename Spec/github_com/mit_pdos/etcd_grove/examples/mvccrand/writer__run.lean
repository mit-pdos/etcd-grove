/- Lean-first (no Rocq counterpart).

`w.run(ops)` (`examples/mvccrand/mvccrand.go`): the writer's loop, `ops` operations (put, range
delete, transaction, grant, revoke, `Commit`, the leases' check, read; each checked), the `n`-th
applying the index `n + 1` (`applying`), sending the published revision on the ticks channel every
so many operations (`isTicks`, its producer's end `ticksW`: each value a published revision,
positive), then closing it. Started between operations (`writerOwn`, the lessor's `writerLe`), the
hook's counters at index `0`, with enough room for the values (`vals`, at most three per operation),
the lease ids (`nextID`, at most one per operation) and the lessor's write tokens (one per
operation); ends between operations at index `ops`, the channel closed.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.WriterRun

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
abbrev writer.run.spec : Prop :=
  ∀ (w : Loc) (wv : writer) (γ : RandNames) (B : KBReal) (f : GoFunc) (q : Qp) (σ : MvccState)
    (Hs : List HRev) (L : List w64) (nid : w64) (k : Nat) (T R : IProp GF) (s v ops : w64)
    (γt : SpscNames),
  0 ≤ sint.Z ops → sint.Z ops < 2 ^ 62 → sint.Z ops ≤ k →
  0 ≤ sint.Z v → sint.Z v + 3 * sint.Z ops < 2 ^ 63 → sint.Z nid + sint.Z ops < 2 ^ 63 →
  {{ writerCtx w wv γ (etcdStorage B) f ∗ writerOwn wv γ (etcdStorage B) q σ Hs L ∗
      writerLe w wv γ B f L nid k T R ∗ hookPre wv (W64 0) s ∗ wF go!"vals" w ↦ v ∗
      ticksW γt wv.ticks' γ }}
    (App (Val (w @!! go.GoType.PointerType writer.ty @!! go!"run")) (Val #ops))
  {{ RET #(); runSt w wv γ B f q T R ops (sint.Z v + 3 * sint.Z ops) (sint.Z nid + sint.Z ops) 0 }}

end spec

end mvccrand
end EtcdGrove
end Perennial
