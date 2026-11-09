/-
## `Interface.AddReadonlyTXID(tid)` (`shared.go`)

**Users.** db.go:896 (`beginTx`, under `metalock`, while a writer may use the freelist). Snippet `ReqReleaseSafe`.
**Proof sketch.** the bundle's triple: the dynamic type is a `*array` or a `*hashMap` (`flOwn`'s realization), whose method (or `shared`'s, promoted) is proved against the realization's invariant; an `append` to `readonlyTXIDs` (`flReaders`' field only).
**Changes.** new: the readers are their own resource (`flReaders`), separate from `flOwn`, so that `beginTx` needs no writer access (the old `flRoOwn`).
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

/-- `f.AddReadonlyTXID(tid)`: `tid` is one more reader. -/
def Interface.AddReadonlyTXID.spec : Prop :=
  ∀ (fl : GoInterface) (R : List Txid) (tid : Txid),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flReaders fl R }}
    (App (flCall fl go!"AddReadonlyTXID") (Val #tid))
  {{ RET #(); flReaders fl (R ++ [tid]) }}

end spec

end Freelist
end EtcdGrove
end Perennial
