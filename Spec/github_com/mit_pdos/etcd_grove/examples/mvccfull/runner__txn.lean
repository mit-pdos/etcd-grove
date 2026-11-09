/- Lean-first (no Rocq counterpart).

`x.txn(m, o, lead, i)` (`examples/mvccfull/mvccfull.go`, the server's `txn.Txn`): the log's
transaction `o` on member `m` (`memCore` at `v.ops` operations; `m.ops` already moved by `apply`, the
hook's index `applying` at `i = v.ops + 1`, `saved` below it): without a write, a concurrent read
transaction made read-only, its compare and ranges checked, no change; with one, the compare in a
shared-buffer read transaction (ended) or in the write transaction, then the sub-operations
(`writeSub`), the changes non-empty iff the model's, `end`. Afterwards the member is at the model
after `v.ops + 1`; the hook saved `i` if a write transaction began (`hookPost`), else nothing ran.
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
abbrev runner.txn.spec : Prop :=
  ∀ (x : Loc) (ks : List GoString) (cfg : Config) (wr : List w64) (h : Loc) (γh : HistNames)
    (ops : List OpM) (i : Nat) (mp : Loc) (m : MemberNames) (f : GoFunc) (v : MemS)
    (qw qk : Qp) (nw k : Nat) (p : Loc) (o : OpM) (lead : Bool) (a s : w64),
  ops[v.ops]? = some o → o.kind = kTxn → logOk ks ops → 1 ≤ nw → ops.length < 2 ^ 38 →
  a = W64 (v.ops + 1 : Int) → sint.Z s < sint.Z a →
  {{ writerCtx (GF := GF) x ks cfg wr h γh ∗ histRd h γh ∗ opIs p o ∗
      memCore ks γh ops i mp m f v qw qk nw k ∗ hookPre mp a s ∗ leadPre γh ks ops v.ops lead }}
    (App (App (App (App (x @!! go.GoType.PointerType runner.ty @!! go!"txn") (Val #mp)) (Val #p)) (Val #lead)) (Val #a))
  {{ RET #(); histRd h γh ∗ leadPost γh ks ops v.ops lead ∗ (hookPost mp a ∨ hookPre mp a s) ∗
      ∃ v' : MemS, ⌜MemS.sameInc v v' ∧ v'.ops = v.ops + 1⌝ ∗
        memCore ks γh ops i mp m f v' qw qk nw k }}

end spec

end mvccfull
end EtcdGrove
end Perennial
