/- Lean-first (no Rocq counterpart).

`x.begin(m)` (`examples/mvccfull/mvccfull.go`): the model of a write transaction on member `m` at
the store state `σ` (nothing pending; its revisions `Hs`, a lower bound of the history): the next
revision, a copy of the last revision's state, no change. It raises `m.revHi` to the next revision
first (opening the incarnation's invariant with the writer's part, `incW`: the bound above the
revision any write in flight can show, and `|σ.notifiedLog| ≤ revHi + 1` for the pending revision's
responses). The new `revHi` stays below `2 ^ 62` (`memberState`'s ceiling): `σ.rev + 2 < 2 ^ 62`,
which the writer has from `Ops < 2 ^ 38` (a revision per operation at most).
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
abbrev runner.begin.spec : Prop :=
  ∀ (x : Loc) (ks : List GoString) (h : Loc) (γh : HistNames) (i : Nat) (mp : Loc)
    (m : MemberNames) (ι : IncNames) (kv : GoInterface) (qw : Qp) (σ : MvccState) (b : Bnd)
    (Hs : List HRev),
  Hs.length = σ.log.length → σ.pending = none → σ.rev + 2 < 2 ^ 62 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗ runnerH x h ∗ histRd h γh ∗ monoListLbOwn γh.l Hs ∗
      mF go!"rev" mp ↦ (W64 (σ.rev : Int)) ∗ incW ks γh i mp m ι kv qw σ b }}
    (App (x @!! go.GoType.PointerType runner.ty @!! go!"begin") (Val #mp))
  {{ (p : Loc), RET #p; histRd h γh ∗ mF go!"rev" mp ↦ (W64 (σ.rev : Int)) ∗
      incW ks γh i mp m ι kv qw σ (b.1, W64 (σ.rev + 1 : Int), b.2.2) ∗
      ownPending p ⟨W64 (Hs.length : Int), lastSt Hs, []⟩ }}

end spec

end mvccfull
end EtcdGrove
end Perennial
