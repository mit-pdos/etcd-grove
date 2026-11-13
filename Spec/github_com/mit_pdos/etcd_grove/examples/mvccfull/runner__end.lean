/- Lean-first (no Rocq counterpart).

`x.end(m, p, lead, end)` (`examples/mvccfull/mvccfull.go`): member `m` ends its write transaction
(begun at the store state `σ`, its revisions `Hs`, mvcc's pending changes `pend`, their model `P` at
`p`, `pendOk`): the leader appends the pending revision to the history if it has a change (the
history's writer part, the check that the history is at its revision, the `revisions` counter); the
follower and the builder hold a lower bound with it. It runs `end` (`endCb`: the store's `End`, or the
revoke's closure; `E`, `E'` the caller's), checks the store's revision (`m.kv.Rev()`) and publishes it
(`m.rev`, `revLo`, `revHi`). Afterwards the store is at `commitSt σ pend` and the bounds at its
revision (`memberState`'s `1 ≤ revLo` and `revHi < 2 ^ 62` kept: the new revision is at least `σ`'s,
and at most `begin`'s `revHi`, `σ.rev + 1`, which the invariant bounds).
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
abbrev runner.end.spec : Prop :=
  ∀ (x : Loc) (ks : List GoString) (h : Loc) (γh : HistNames) (i : Nat) (mp : Loc)
    (m : MemberNames) (ι : IncNames) (kv : GoInterface) (qw : Qp) (σ : MvccState) (b : Bnd)
    (Hs : List HRev) (Cs : List w64) (p : Loc) (P : PendM) (pend : List Change) (e : GoFunc)
    (E E' : IProp GF) (lead : Bool),
  pendOk ks σ Hs pend P → Hs.length = σ.log.length → σ.pending = none →
  sint.Z b.2.1 = σ.rev + 1 → σ.rev + 2 < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ runnerH x h ∗ ctrInv (readersN .@ "revisions") (rF go!"revisions" x) ∗
      histRd h γh ∗ mF go!"rev" mp ↦ (W64 (σ.rev : Int)) ∗ mF go!"kv" mp ↦{DFrac.own qw} kv ∗
      incW ks γh i mp m ι kv qw σ b ∗ ownPending p P ∗
      (if lead then histW γh Hs Cs else monoListLbOwn γh.l (histAfter Hs P)) ∗
      endCb e ks γh i mp m ι kv qw σ b pend (histAfter Hs P) E E' ∗ E }}
    (App (App (App (App (x @!! go.GoType.PointerType runner.ty @!! go!"end") (Val #mp)) (Val #p)) (Val #lead)) (Val #e))
  {{ RET #(); histRd h γh ∗ mF go!"rev" mp ↦ (W64 ((commitSt σ pend).rev : Int)) ∗
      mF go!"kv" mp ↦{DFrac.own qw} kv ∗
      incW ks γh i mp m ι kv qw (commitSt σ pend)
        (W64 ((commitSt σ pend).rev : Int), W64 ((commitSt σ pend).rev : Int), b.2.2) ∗
      mvccReaders ι.kv 1 ∗ E' ∗ (if lead then histW γh (histAfter Hs P) Cs else iprop(True)) }}

end spec

end mvccfull
end EtcdGrove
end Perennial
