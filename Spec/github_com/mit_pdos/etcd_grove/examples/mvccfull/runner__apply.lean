/- Lean-first (no Rocq counterpart).

`x.apply(m, o, lead)` (`examples/mvccfull/mvccfull.go`): member `m` (the `i`-th: the leader, the
follower or a builder; `memW`, `Writer.lean`) applies the log's next operation `o` (`ops[v.ops]`, at
`p`, `opIs`), every result checked against the model: `m.ops` and the hook's index `applying` move to
`v.ops + 1`; a put, a range delete, a transaction (`txn`), a lease grant, a revoke (the lease's keys
deleted in one revision through the lessor's range deleter, `end`'s callback), a compaction
(`compact`), a `Commit`, a read at the member's revision, or the lessor's check (`checkLeases`). The
leader (`lead`) appends the revision to the history (`leadPre`/`leadPost`: the history's writer part);
the follower and the builder find it there. **Every check passes**: afterwards the member is at the
model after `v.ops + 1` operations (the same incarnation and files, `MemS.sameInc`), at most one
write-back token spent (a grant's). The log is valid (`logOk`). (F1 Prove, 2026-11-10: the caller's
thread token and the bounds' classes, lent to `checkLeases`.)
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
abbrev runner.apply.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 38)] (x : Loc) (ks : List GoString) (cfg : Config) (wr : List w64) (h : Loc) (γh : HistNames)
    (ops : List OpM) (i : Nat) (mp : Loc) (m : MemberNames) (f : GoFunc) (v : MemS)
    (qw : Qp) (nw k : Nat) (p : Loc) (o : OpM) (lead : Bool),
  ops[v.ops]? = some o → logOk ks ops → 1 ≤ nw → (o.kind = kGrant → 1 ≤ k) → ops.length < 2 ^ 38 →
  {{ writerCtx (GF := GF) x ks cfg wr h γh ∗ histRd h γh ∗ opIs p o ∗
      memW ks γh ops i mp m f v qw nw k ∗ leadPre γh ks ops v.ops lead ∗ threadTok }}
    (App (App (App (x @!! go.GoType.PointerType runner.ty @!! go!"apply") (Val #mp)) (Val #p)) (Val #lead))
  {{ RET #(); histRd h γh ∗ leadPost γh ks ops v.ops lead ∗ threadTok ∗
      ∃ (v' : MemS) (k' : Nat), ⌜MemS.sameInc v v' ∧ v'.ops = v.ops + 1 ∧ k ≤ k' + 1⌝ ∗
        memW ks γh ops i mp m f v' qw nw k' }}

end spec

end mvccfull
end EtcdGrove
end Perennial
