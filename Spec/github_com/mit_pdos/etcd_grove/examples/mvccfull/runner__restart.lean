/- Lean-first (no Rocq counterpart).

`x.restart(m)` (`examples/mvccfull/mvccfull.go`): member `m` (the `j`-th of the run's) restarts,
as its process would: the readers stopped (both members': `stopReaders`, the stock back), its streams
drained and closed (`endEpoch`, the epoch's tokens back), then the chain (`Writer.lean`'s header):
retire (`inc_retire`, every share back), `shut`, `open` (a new incarnation); the `restarts` counter;
the streams and readers started again on the members' current incarnations. Every check passes.
Afterwards the writer is between steps again (`writerOwn`) with both members at the same counts.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Writer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- See the file header. -/
abbrev runner.restart.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 38)] (x : Loc) (ks : List GoString)
    (cfg : Config) (wr : List w64) (h : Loc) (γ : FullNames) (mp0 mp1 : Loc) (f0 f1 : GoFunc)
    (ops : List OpM) (v0 v1 : MemS) (nv nb : Nat) (q qs : Qp) (j : Nat) (mp : Loc),
  [mp0, mp1][j]? = some mp → backend.dbOpenOk → backend.dbCloseOk →
  ckptEffectsOk → sint.Z (limOf cfg) ≤ 2 ^ 57 → batchLimitOk (cblOf cfg) →
  {{ writerCtx (GF := GF) x ks cfg wr h γ.h ∗
      envVerifyOff ∗ threadTok ∗ writerOwn x ks cfg h γ mp0 mp1 f0 f1 ops v0 v1 nv nb q qs }}
    (App (x @!! go.GoType.PointerType runner.ty @!! go!"restart") (Val #mp))
  {{ RET #(); threadTok ∗
      ∃ (v0' v1' : MemS) (q' qs' : Qp), ⌜v0'.ops = v0.ops ∧ v1'.ops = v1.ops⌝ ∗
        writerOwn x ks cfg h γ mp0 mp1 f0 f1 ops v0' v1' nv nb q' qs' }}

end spec

end mvccfull
end EtcdGrove
end Perennial
