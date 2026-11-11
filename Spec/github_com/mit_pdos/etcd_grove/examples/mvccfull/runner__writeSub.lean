/- Lean-first (no Rocq counterpart).

`x.writeSub(m, tw, p, s)` (`examples/mvccfull/mvccfull.go`): one sub-operation `s` (`subIs`) of a
write transaction `tw` (as `writeRange`'s, the lessor's owner part at the pending items): a put (its
key one of the keys, no earlier change's; its lease `0` or live), a range delete (no earlier put in
its range: `subFresh`), or a range read (`writeRange`), every result checked. Afterwards the
transaction has the changes `pend ++ pend'`, the model `subStep ks P s` of them (`pendOk`, the read
log well formed), the owner's part at the new pending items, the transaction's trace back (lent to
`Put`, `DeleteRange` or `Range`, as their contracts do).
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
abbrev runner.writeSub.spec : Prop :=
  ∀ (x : Loc) (ks : List GoString) (h : Loc) (γh : HistNames) (mp : Loc) (γk : MvccName)
    (tw : GoInterface) (trace : Loc) (te : Bool) (σ : MvccState) (pend : List Change) (Hs : List HRev)
    (p : Loc) (P : PendM) (sv : subOp) (sm : SubM) (L : List w64),
  pendOk ks σ Hs pend P → Hs.length = σ.log.length → HistRevs ks σ.log Hs → MvccReachable σ →
  txn.LogOk (σ.log ++ [pend]) → σ.log.length + 3 ≤ 2 ^ 63 → pend.length + ks.length < 2 ^ 62 →
  subFresh P.chs sm → (sm.kind = W64 0 → sm.key ∈ ks ∧ (sm.lease = W64 0 ∨ sm.lease ∈ L)) →
  (∀ k ∈ ks, (k.length : Int) < 2 ^ 63 - 1) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ runnerKeys x ks ∗ runnerH x h ∗ histRd h γh ∗ monoListLbOwn γh.l Hs ∗
      mF go!"cmp" mp ↦ (W64 σ.crev) ∗ mvccTxn tw γk trace (.write σ pend) ∗ traceutil.ownTrace trace te ∗
      ownPending p P ∗
      subIs sv sm ∗ lease.leaseOwn (mvccLeases γk) L (pendItems σ.log pend) }}
    (App (App (App (App (x @!! go.GoType.PointerType runner.ty @!! go!"writeSub") (Val #mp)) (Val #tw)) (Val #p)) (Val #sv))
  {{ RET #(); histRd h γh ∗ mF go!"cmp" mp ↦ (W64 σ.crev) ∗
      ∃ pend' : List Change, ⌜pendOk ks σ Hs (pend ++ pend') (subStep ks P sm) ∧
        txn.LogOk (σ.log ++ [pend ++ pend']) ∧ pend'.length ≤ ks.length⌝ ∗
      mvccTxn tw γk trace (.write σ (pend ++ pend')) ∗ traceutil.ownTrace trace te ∗
      ownPending p (subStep ks P sm) ∗
      lease.leaseOwn (mvccLeases γk) L (pendItems σ.log (pend ++ pend')) }}

end spec

end mvccfull
end EtcdGrove
end Perennial
