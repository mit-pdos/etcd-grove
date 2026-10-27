/-
The store over the thread-safe store (`cache`, `tools/cache/store.go`): an `Indexer`/`Store` whose
keys a key function computes. Lean-first.

* `keyOk D kf KF`: a key function's contract: on an object meeting `D`, `kf` returns the key
  `KF o` and no error (`MetaNamespaceKeyFunc`: `ns/name`). The store's methods take it per call,
  for the call's objects (`D`: the call's objects, `KF` their keys): a key is a function of an
  object's contents in the heap, which no pure `KF` fixed in advance can give for objects allocated
  later (2026-10-27; `notes/STATUS.md`, "Keys and resource versions per call").
* `isCache ca ts γ OK Fam kf` (persistent): `ca` is a `*cache` over the thread-safe store `ts`
  (`isTS`), with key function `kf` and no transformer. Its readers use `ts`'s reader slots
  (`tsReader ts γ OK Fam`).
-/
module

public import Proof.k8s_io.client_go.tools.cache.TSDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- **The key function's contract**: on an object meeting `D`, the key `KF o` and no error. -/
def keyOk (D : GoInterface → IProp GF) (kf : GoFunc) (KF : GoInterface → GoString) : IProp GF :=
  iprop(∀ o : GoInterface, {{ □ D o }} (App (Val #kf) (Val #o))
    {{ (k : GoString) (err : GoInterface), RET (PairV #k #err); ⌜k = KF o ∧ err = interface.nil⌝ }})

instance keyOk_persistent (D : GoInterface → IProp GF) (kf : GoFunc) (KF : GoInterface → GoString) :
    Persistent (keyOk D kf KF) := by
  unfold keyOk; infer_instance

/-- The items `Replace(list, rv)` builds: each object at its key, a later one at a key winning. -/
def keyedItems (KF : GoInterface → GoString) (xs : List GoInterface) : Items :=
  xs.foldl (fun m x => <[KF x := x]> m) ∅

/-- **The store** (persistent): `ca` over the thread-safe store `ts`. -/
def isCache (ca ts : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn)
    (kf : GoFunc) : IProp GF :=
  iprop(structFieldRef cache go!"cacheStorage" ca ↦□
      interface.mkOk (go.GoType.PointerType threadSafeMap.ty) #ts ∗
    structFieldRef cache go!"keyFunc" ca ↦□ kf ∗
    structFieldRef cache go!"transformer" ca ↦□ func.nil ∗
    isTS ts γ OK Fam)

instance isCache_persistent (ca ts : Loc) (γ : TsNames) (OK : GoInterface → IProp GF)
    (Fam : Nat → Fn) (kf : GoFunc) :
    Persistent (isCache (GF := GF) ca ts γ OK Fam kf) := by
  unfold isCache; infer_instance

end defs

end cache
end EtcdGrove
end Perennial
