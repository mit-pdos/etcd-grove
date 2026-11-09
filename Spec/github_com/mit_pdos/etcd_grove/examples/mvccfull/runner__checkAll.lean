/- Lean-first (no Rocq counterpart).

`x.checkAll(m)` (`examples/mvccfull/mvccfull.go`): member `m` (reopened: `memCore`) reads every
revision not compacted, in full, in one read transaction, and the one below the compaction revision
(which must fail with `ErrCompacted`); each against the history (`checkRangeAt`). Every check passes;
nothing changes.
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
abbrev runner.checkAll.spec : Prop :=
  ∀ (x : Loc) (ks : List GoString) (cfg : Config) (wr : List w64) (h : Loc) (γh : HistNames)
    (ops : List OpM) (i : Nat) (mp : Loc) (m : MemberNames) (f : GoFunc) (v : MemS)
    (qw : Qp) (nw k : Nat),
  logOk ks ops → 1 ≤ nw → ops.length < 2 ^ 38 →
  {{ writerCtx (GF := GF) x ks cfg wr h γh ∗ histRd h γh ∗ monoListLbOwn γh.l (histAt ks ops v.ops) ∗
      memCore ks γh ops i mp m f v qw nw k }}
    (App (x @!! go.GoType.PointerType runner.ty @!! go!"checkAll") (Val #mp))
  {{ RET #(); histRd h γh ∗ memCore ks γh ops i mp m f v qw nw k }}

end spec

end mvccfull
end EtcdGrove
end Perennial
