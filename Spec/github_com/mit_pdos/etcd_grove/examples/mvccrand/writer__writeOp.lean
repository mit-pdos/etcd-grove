/- Lean-first (no Rocq counterpart).

`w.writeOp(tw, p)` (`examples/mvccrand/mvccrand.go`): one operation of a write transaction `tw`
(begun at the store's state `σ`, never compacted, the writer between transactions at `σ` and the
history `Hs`, `writerIdle`), whose changes so far are `pend` and the tester's model of them `P` at
`p` (`pendOk`, the read log well formed, `txn.LogOk`): a put (with no lease or a live one), a range
delete or a range read, every result checked. After it the transaction has the changes
`pend ++ pend'` (at most six more: a delete removes at most the tester's six keys), the model
`P'` of them (`pendOk`, `LogOk` kept), and at most one value was drawn (`vals`). The writer's
generator, its leases' map and mvcc's lease ownership (at the pending items) are threaded through.
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
abbrev writer.writeOp.spec : Prop :=
  ∀ (w : Loc) (wv : writer) (γ : RandNames) (B : MvccStorage) (f : GoFunc) (σ : MvccState)
    (Hs : List HRev) (L : List w64) (tw : GoInterface) (trace : Loc) (te : Bool) (p : Loc)
    (P : PendM) (pend : List Change) (n : w64),
  pendOk σ Hs pend P → txn.LogOk (σ.log ++ [pend]) → σ.crev = -1 → 1 ≤ σ.rev →
  pend.length + 6 < 2 ^ 63 → 0 ≤ sint.Z n → sint.Z n + 1 < 2 ^ 63 →
  {{ writerCtx w wv γ B f ∗ histRd wv.h' γ.h ∗ writerIdle γ σ Hs ∗
      mvccTxn tw γ.kv trace (.write σ pend) ∗ traceutil.ownTrace trace te ∗ ownPending p P ∗
      (∃ g : rng, (wv.r' ↦ g : IProp GF)) ∗
      (∃ Lm : GMap w64 Bool, wv.leases' ↦$ Lm ∗ ⌜∀ id, (Lm !! id).isSome = true ↔ id ∈ L⌝) ∗
      lease.leaseOwn (mvccLeases γ.kv) L (pendItems σ.log pend) ∗ wF go!"vals" w ↦ n }}
    (App (App (Val (w @!! go.GoType.PointerType writer.ty @!! go!"writeOp")) (Val #tw)) (Val #p))
  {{ RET #(); ∃ (pend' : List Change) (P' : PendM) (n' : w64),
      ⌜pendOk σ Hs (pend ++ pend') P' ∧ txn.LogOk (σ.log ++ [pend ++ pend']) ∧ pend'.length ≤ 6 ∧
        (n' = n ∨ n' = n + W64 1)⌝ ∗
      histRd wv.h' γ.h ∗ writerIdle γ σ Hs ∗
      mvccTxn tw γ.kv trace (.write σ (pend ++ pend')) ∗ traceutil.ownTrace trace te ∗
      ownPending p P' ∗ (∃ g : rng, (wv.r' ↦ g : IProp GF)) ∗
      (∃ Lm : GMap w64 Bool, wv.leases' ↦$ Lm ∗ ⌜∀ id, (Lm !! id).isSome = true ↔ id ∈ L⌝) ∗
      lease.leaseOwn (mvccLeases γ.kv) L (pendItems σ.log (pend ++ pend')) ∗ wF go!"vals" w ↦ n' }}

end spec

end mvccrand
end EtcdGrove
end Perennial
