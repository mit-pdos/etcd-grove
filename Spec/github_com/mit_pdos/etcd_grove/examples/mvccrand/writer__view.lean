/- Lean-first (no Rocq counterpart).

`w.view(p)` (`examples/mvccrand/mvccrand.go`): inside a write transaction (the writer at its
revisions `Hs`, `writerIdle`, the pending model `P` at `p`, revision `len(Hs)`), the states a read in
the transaction sees and its revision: the history's states with the pending one appended once it
has a change (`viewSt`, the history's persistent, the pending one owned, `viewDq`), at the pending
revision then, else at the last (`viewRev`). The pending map is lent to the states: given back
(`ownPending p P`) once they are.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.Writer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- See the file header. -/
abbrev writer.view.spec : Prop :=
  ∀ (w : Loc) (wv : writer) (γ : RandNames) (σ : MvccState) (Hs : List HRev) (p : Loc) (P : PendM),
  P.rev = W64 (Hs.length : Int) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand ∗
      writerRO w wv ∗ histRd wv.h' γ.h ∗ writerIdle γ σ Hs ∗ ownPending p P }}
    (App (Val (w @!! go.GoType.PointerType writer.ty @!! go!"view")) (Val #p))
  {{ (s : GoSlice) (cur : w64), RET (PairV #s #cur); histRd wv.h' γ.h ∗ writerIdle γ σ Hs ∗
      ⌜cur = viewRev P⌝ ∗ ∃ (dsl : DFrac) (ms : List GoMap), s ↦*{dsl} ms ∗
        statesAt ms (viewSt Hs P) (viewDq Hs P) ∗
        (statesAt ms (viewSt Hs P) (viewDq Hs P) -∗ ownPending p P) }}

end spec

end mvccrand
end EtcdGrove
end Perennial
