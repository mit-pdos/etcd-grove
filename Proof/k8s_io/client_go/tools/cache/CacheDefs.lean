/-
The store over the thread-safe store (`cache`, `tools/cache/store.go`): an `Indexer`/`Store` whose
keys a key function computes. Lean-first.

* `keyOk OK kf KF`: the key function's contract: on an object meeting `OK`, `kf` returns the key
  `KF o` and no error (`MetaNamespaceKeyFunc`: `ns/name`; the client discharges it).
* `isCache ca ts γ OK Fam KF` (persistent): `ca` is a `*cache` over the thread-safe store `ts`
  (`isTS`), with key function `kf` meeting `keyOk` and no transformer. Its readers use `ts`'s
  reader slots (`tsReader ts γ OK Fam`).
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

/-- **The key function's contract**: on an object meeting `OK`, the key `KF o` and no error. -/
def keyOk (OK : GoInterface → IProp GF) (kf : GoFunc) (KF : GoInterface → GoString) : IProp GF :=
  iprop(∀ o : GoInterface, {{ □ OK o }} (App (Val #kf) (Val #o))
    {{ (k : GoString) (err : GoInterface), RET (PairV #k #err); ⌜k = KF o ∧ err = interface.nil⌝ }})

instance keyOk_persistent (OK : GoInterface → IProp GF) (kf : GoFunc) (KF : GoInterface → GoString) :
    Persistent (keyOk OK kf KF) := by
  unfold keyOk; infer_instance

/-- **The store** (persistent): `ca` over the thread-safe store `ts`. -/
def isCache (ca ts : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn)
    (KF : GoInterface → GoString) : IProp GF :=
  iprop(∃ kf : GoFunc,
    structFieldRef cache go!"cacheStorage" ca ↦□
      interface.mkOk (go.GoType.PointerType threadSafeMap.ty) #ts ∗
    structFieldRef cache go!"keyFunc" ca ↦□ kf ∗
    structFieldRef cache go!"transformer" ca ↦□ func.nil ∗
    keyOk OK kf KF ∗ isTS ts γ OK Fam)

instance isCache_persistent (ca ts : Loc) (γ : TsNames) (OK : GoInterface → IProp GF)
    (Fam : Nat → Fn) (KF : GoInterface → GoString) :
    Persistent (isCache (GF := GF) ca ts γ OK Fam KF) := by
  unfold isCache; infer_instance

end defs

end cache
end EtcdGrove
end Perennial
