/- Lean-first (no Rocq counterpart).

`x.checkLeases(m)` (`examples/mvccfull/mvccfull.go`): member `m` (`memCore`) checks its lessor
against the model at its revision (the history's state `m.rev`, a lower bound of which covers the
member's revisions): each key's lease (`GetLease`), the number of live leases (`Leases`), and each
model lease's keys (`Lookup` not `nil`, `Keys()` sorted, against the keys on it in order). Every check
passes; nothing changes. (F1 Prove, 2026-11-10: the caller's thread token and the thread and receipt
bounds (`ThreadBoundLe`, `ReceiptBoundLe`, as `write`'s), which `Leases()`'s sort takes; the reader pool is `lessorW`'s.)
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
abbrev runner.checkLeases.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 38)] (x : Loc) (ks : List GoString) (cfg : Config) (wr : List w64) (h : Loc) (γh : HistNames)
    (ops : List OpM) (i : Nat) (mp : Loc) (m : MemberNames) (f : GoFunc) (v : MemS)
    (qw : Qp) (nw k : Nat),
  logOk ks ops →
  {{ writerCtx (GF := GF) x ks cfg wr h γh ∗ histRd h γh ∗ monoListLbOwn γh.l (histAt ks ops v.ops) ∗
      memCore ks γh ops i mp m f v qw nw k ∗ threadTok }}
    (App (x @!! go.GoType.PointerType runner.ty @!! go!"checkLeases") (Val #mp))
  {{ RET #(); histRd h γh ∗ memCore ks γh ops i mp m f v qw nw k ∗ threadTok }}

end spec

end mvccfull
end EtcdGrove
end Perennial
