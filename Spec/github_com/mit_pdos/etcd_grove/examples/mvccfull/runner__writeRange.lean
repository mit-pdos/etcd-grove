/- Lean-first (no Rocq counterpart).

`x.writeRange(m, tw, p, q)` (`examples/mvccfull/mvccfull.go`): a range read `q` in the write
transaction `tw` (begun at the store state `σ`, mvcc's pending changes `pend`, their model `P` at
`p`, `pendOk`; the member's revisions `Hs` cover `σ`'s log), checked against the view
(`view`, `checkRangeAt`) at the member's compaction revision `m.cmp` (`σ.crev`). Every check passes;
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
abbrev runner.writeRange.spec : Prop :=
  ∀ (x : Loc) (ks : List GoString) (h : Loc) (γh : HistNames) (mp : Loc) (γk : MvccName)
    (tw : GoInterface) (trace : Loc) (σ : MvccState) (pend : List Change) (Hs : List HRev)
    (p : Loc) (P : PendM) (q : rangeReq) (qm : RangeM),
  pendOk ks σ Hs pend P → Hs.length = σ.log.length → HistRevs ks σ.log Hs → MvccReachable σ →
  txn.LogOk (σ.log ++ [pend]) → σ.log.length + 3 ≤ 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ runnerKeys x ks ∗ runnerH x h ∗ histRd h γh ∗ monoListLbOwn γh.l Hs ∗
      mF go!"cmp" mp ↦ (W64 σ.crev) ∗ mvccTxn tw γk trace (.write σ pend) ∗ ownPending p P ∗
      rangeIs q qm }}
    (App (App (App (App (x @!! go.GoType.PointerType runner.ty @!! go!"writeRange") (Val #mp)) (Val #tw)) (Val #p)) (Val #q))
  {{ RET #(); histRd h γh ∗ mF go!"cmp" mp ↦ (W64 σ.crev) ∗ mvccTxn tw γk trace (.write σ pend) ∗
      ownPending p P }}

end spec

end mvccfull
end EtcdGrove
end Perennial
