/- Lean-first (no Rocq counterpart).

`x.view(p)` (`examples/mvccfull/mvccfull.go`): inside a write transaction on a member whose
revisions are `Hs` (a lower bound of the history; the pending model `P` at `p`, revision `|Hs|`), the
states a read in the transaction sees and its revision: the member's states (the history's first
`|Hs|`, persistent) with the pending one appended once it has a change (`viewSt`, `viewDq`), at the
pending revision then, else at the last (`viewRev`). The pending map is lent to the states, given
back (`ownPending p P`) once they are.
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
abbrev runner.view.spec : Prop :=
  ∀ (x : Loc) (h : Loc) (γh : HistNames) (Hs : List HRev) (p : Loc) (P : PendM),
  P.rev = W64 (Hs.length : Int) → 2 ≤ Hs.length → Hs.length < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗ runnerH x h ∗ histRd h γh ∗ monoListLbOwn γh.l Hs ∗ ownPending p P }}
    (App (x @!! go.GoType.PointerType runner.ty @!! go!"view") (Val #p))
  {{ (s : GoSlice) (cur : w64), RET (PairV #s #cur); histRd h γh ∗ ⌜cur = viewRev P⌝ ∗
      ∃ (dsl : DFrac) (ms : List GoMap), s ↦*{dsl} ms ∗
        statesAt ms (viewSt Hs P) (viewDq Hs P) ∗
        (statesAt ms (viewSt Hs P) (viewDq Hs P) -∗ ownPending p P) }}

end spec

end mvccfull
end EtcdGrove
end Perennial
