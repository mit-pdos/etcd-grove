/-
## `Interface.RemoveReadonlyTXID(tid)` (`shared.go`)

**Users.** db.go:957 (`removeTx`, under `metalock`). Snippet `ReqReleaseSafe`.
**Proof sketch.** the bundle's triple: the dynamic type is a `*array` or a `*hashMap` (`flOwn`'s realization), whose method (or `shared`'s, promoted) is proved against the realization's invariant; the first occurrence swapped with the last and dropped (a multiset removal, `flReaders_perm`).
**Changes.** new (as `AddReadonlyTXID`).
**Margin.** none: the post is what the code computes.
-/
module

public import Spec.go_etcd_io.bbolt.internal.freelist.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Freelist

open Iris Iris.BI go_etcd_io.bbolt.internal.common BboltCommon

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `f.RemoveReadonlyTXID(tid)`: one occurrence of `tid` is no longer a reader (none if it is not one). -/
def Interface.RemoveReadonlyTXID.spec : Prop :=
  ∀ (fl : GoInterface) (R : List Txid) (tid : Txid),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flReaders fl R }}
    (App (flCall fl go!"RemoveReadonlyTXID") (Val #tid))
  {{ RET #(); flReaders fl (R.erase tid) }}

end spec

end Freelist
end EtcdGrove
end Perennial
