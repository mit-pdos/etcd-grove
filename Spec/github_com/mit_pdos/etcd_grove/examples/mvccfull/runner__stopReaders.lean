/- Lean-first (no Rocq counterpart).

`x.stopReaders()` (`examples/mvccfull/mvccfull.go`): sets the stop flag and waits for the readers.

**The triple.** With the shared atomics (`rdShared`: the flag's invariant) and the readers' join
(`sync.tokJoin.ownAdder rdWgN False x.readWg n P`, `startReaders`' post with `P` the lent stock),
it returns the join at rest and `P` (the readers' `Done`s' resources, later than the store: `▷`).
The flag's value carries nothing the proof needs (a reader that misses it only reads more). The
spec is the wait group's (`P` any), so the caller's stock is whatever it lent.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Readers

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- See the file header. -/
abbrev runner.stopReaders.spec : Prop :=
  ∀ (x : Loc) (n : Nat) (P : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗
      rdShared x ∗ sync.tokJoin.ownAdder rdWgN iprop(False) (rF go!"readWg" x) n P }}
    (App (x @!! go.GoType.PointerType runner.ty @!! go!"stopReaders") (Val #()))
  {{ RET #(); sync.tokJoin.ownAdder rdWgN iprop(False) (rF go!"readWg" x) 0 iprop(True) ∗ ▷ P }}

end spec

end mvccfull
end EtcdGrove
end Perennial
