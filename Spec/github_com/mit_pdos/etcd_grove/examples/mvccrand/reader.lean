/- Lean-first (no Rocq counterpart).

`reader(kv, h, r, reads)` (`examples/mvccrand/mvccrand.go`): `reads` reads concurrent with the
writer (`Rev`, read transactions, read-only transactions), each checked against the history
(`history.seen`, `checkRange`). Given the store's handle, the tester's invariant (`worldInv`,
`World.lean`) and the thread's handle of the history (`histRd`), it returns: every check passes.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.World
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO

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
abbrev reader.spec : Prop :=
  ∀ (kv : GoInterface) (h r : Loc) (γ : RandNames) (g : rng) (reads : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil ∗
      isMvcc kv γ.kv ∗ inv worldN (worldInv h γ) ∗ histRd h γ.h ∗ threadTok ∗ mvccReaders γ.kv 1 ∗ r ↦ g }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccrand.reader)) (Val #kv))
      (Val #h)) (Val #r)) (Val #reads))
  {{ RET #(); histRd h γ.h ∗ threadTok ∗ mvccReaders γ.kv 1 ∗ ∃ g' : rng, r ↦ g' }}

end spec

end mvccrand
end EtcdGrove
end Perennial
