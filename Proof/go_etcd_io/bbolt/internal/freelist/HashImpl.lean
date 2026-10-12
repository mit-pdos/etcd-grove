/-
The `hashMap` freelist as an implementation of the freelist interface (`FLImpl`):
`hashMapImpl h`, its own part `ownHashMap h s free` a consistent `hashMap` at `h` holding the
free ids `free` (`ownHashPart`, `HashModel.lean`), with the package initialized and the free ids
at least 2.

The package is part of the predicate (unlike `array`'s, `HashModel.lean`'s `hashImpl`) because
`hashMap.FreeCount` calls `common.Verify`, which needs it, and `FLImpl.FreeCountSpec` and
`FLImpl.FreePageIdsSpec` give the method only `I.own s free`. The free ids are at least 2
(as in a well-formed `FLState`) because `mergeWithExistingSpan` looks up the span after the
last id it merges, which wraps around to `0` past `2^64-1`: no span may start at `0`.
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.HashLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.freelist

section preds
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- The `hashMap` at `h` holds the free ids `free` (at least 2), the package initialized. -/
def ownHashMap (h : Loc) (s : Loc) (free : List w64) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗
    ownHashPart h s free ∗ ⌜∀ x ∈ free, 2 ≤ uint.Z x⌝)

/-- The `hashMap` at `h` as an implementation of the freelist interface. -/
def hashMapImpl (h : Loc) : FLImpl (GF := GF) :=
  ⟨go.GoType.PointerType hashMap.ty, #h, ownHashMap h, hashHdl h,
    fun _ => by unfold hashHdl; infer_instance⟩

theorem hashMapImpl.ity (h : Loc) :
    (hashMapImpl (GF := GF) h).ity = go.GoType.PointerType hashMap.ty := rfl
theorem hashMapImpl.iv (h : Loc) : (hashMapImpl (GF := GF) h).iv = #h := rfl

end preds

end bbolt
end EtcdGrove
end Perennial
