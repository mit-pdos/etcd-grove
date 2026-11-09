/- Lean-first (no Rocq counterpart).

`x.write()` (`examples/mvccfull/mvccfull.go`): the writer's loop until the leader has applied
`cfg.Ops` operations, each step by `Mix.Step`: the leader applies a new operation (`gen`, appended to
the log, `apply` leading), the follower applies the next one, the follower installs a snapshot
(`restore`), a member restarts (`restart`), or the lessors are checked; then the follower catches up.
Every check passes. Started between steps (`writerOwn`, at most `cfg.Ops` operations in the log),
afterwards the log extended to exactly `cfg.Ops` operations, both members at its end.
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
abbrev runner.write.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 38)] (x : Loc) (ks : List GoString)
    (cfg : Config) (wr : List w64) (h : Loc) (γ : FullNames) (mp0 mp1 : Loc) (f0 f1 : GoFunc)
    (ops : List OpM) (v0 v1 : MemS) (nv nb : Nat) (q qs : Qp),
  ops.length ≤ (sint.Z cfg.Ops').toNat → sint.Z cfg.Ops' < 2 ^ 38 → nv + 3 * (sint.Z cfg.Ops').toNat < 2 ^ 62 →
  backend.dbOpenOk → backend.dbCloseOk → ckptEffectsOk →
  sint.Z (limOf cfg) ≤ 2 ^ 57 → batchLimitOk (cblOf cfg) →
  {{ writerCtx (GF := GF) x ks cfg wr h γ.h ∗
      □ (∀ (γB : backend.BNames) (P : backend.BParams) (b' : Loc), keySized γB P b') ∗
      envVerifyOff ∗ threadTok ∗ writerOwn x ks cfg h γ mp0 mp1 f0 f1 ops v0 v1 nv nb q qs }}
    (App (x @!! go.GoType.PointerType runner.ty @!! go!"write") (Val #()))
  {{ RET #(); threadTok ∗
      ∃ (ops' : List OpM) (v0' v1' : MemS) (nv' nb' : Nat) (q' qs' : Qp),
        ⌜ops <+: ops' ∧ ops'.length = (sint.Z cfg.Ops').toNat ∧ v1'.ops = ops'.length⌝ ∗
        writerOwn x ks cfg h γ mp0 mp1 f0 f1 ops' v0' v1' nv' nb' q' qs' }}

end spec

end mvccfull
end EtcdGrove
end Perennial
