/- Lean-first (no Rocq counterpart).

`p.put(k, v, l)` (`examples/mvccfull/mvccfull.go`): the pending transaction's model puts `v` with
lease `l` at `k` (`PendM.put`, `Pending.lean`: the key's create revision kept and its version
bumped if present, else created at the pending revision), its change appended.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Pending

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

/-- See the file header. -/
abbrev pending.put.spec : Prop :=
  ∀ (p : Loc) (P : PendM) (k v : GoString) (l : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗ ownPending p P }}
    (App (App (App (p @!! go.GoType.PointerType pending.ty @!! go!"put") (Val #k)) (Val #v)) (Val #l))
  {{ RET #(); ownPending p (P.put k v l) }}

end spec

end mvccfull
end EtcdGrove
end Perennial
