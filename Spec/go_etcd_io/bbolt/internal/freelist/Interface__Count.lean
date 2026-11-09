/-
## `Interface.Count()` (`shared.go`, `array.go`, `hashmap.go`)

**Users.** tx_check.go:49 (`Check`: the length of `Copyall`'s buffer).
**Proof sketch.** the bundle's triple: the dynamic type is a `*array` or a `*hashMap` (`flOwn`'s realization), whose method (or `shared`'s, promoted) is proved against the realization's invariant; the counts are sums of lengths (an `int`: the bound).
**Changes.** new (no old spec).
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

/-- `f.Count()`: the number of free and pending pages. -/
def Interface.Count.spec : Prop :=
  ∀ (fl : GoInterface) (F : FLState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ flOwn fl F ∗ ⌜F.count < flMaxIds⌝ }}
    (App (flCall fl go!"Count") (Val #()))
  {{ RET #(W64 (F.count : Int)); flOwn fl F }}

end spec

end Freelist
end EtcdGrove
end Perennial
