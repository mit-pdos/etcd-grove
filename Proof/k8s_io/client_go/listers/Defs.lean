/-
The generic lister (`k8s.io/client-go/listers`'s `ResourceIndexer[T]`, `generic_helpers.go`): what
its specs are stated with. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md`.

* `typedOK OK X`: every object the store's contract covers is a non-nil `*X` (the informers' stores
  hold their resource's objects only; a lister's type assertion `obj.(T)` needs it).
* `ptrObj X l`: the object `*X` at `l`, as an interface.
* `riVal ca res ns`: the lister value `ResourceIndexer[*X]{indexer: ca, resource: res,
  namespace: ns}` over the cache `ca`.
* `nsKey ns name`: the store key a namespaced lister looks `name` up at (`ns/name`, or `name`).
-/
module

public import Proof.k8s_io.client_go.tools.cache.ListerDefs
public import GeneratedProof.k8s_io.client_go.listers
public import Proof.k8s_io.client_go.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace listers

open Iris Iris.BI cache

/-- The object `*X` at `l`. -/
def ptrObj [FfiSyntax] [GoGlobalContext] (X : go.GoType) (l : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType X) #l

/-- The lister value over the cache `ca`. -/
def riVal [FfiSyntax] [GoGlobalContext] (ca : Loc)
    (res : k8s_io.apimachinery.pkg.runtime.schema.GroupResource) (ns : GoString) :
    k8s_io.client_go.listers.ResourceIndexer Loc :=
  ⟨interface.mkOk (go.GoType.PointerType k8s_io.client_go.tools.cache.cache.ty) #ca, res, ns⟩

/-- The store key of `name` in namespace `ns` (`generic_helpers.go:59`). -/
def nsKey [FfiSyntax] (ns name : GoString) : GoString :=
  if ns = [] then name else ns ++ go!"/" ++ name

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- Every object meeting `OK` is a `*X`. -/
def typedOK (OK : GoInterface → IProp GF) (X : go.GoType) : IProp GF :=
  iprop(□ ∀ o : GoInterface, OK o -∗ ⌜∃ l : Loc, o = ptrObj X l⌝)

instance typedOK_persistent (OK : GoInterface → IProp GF) (X : go.GoType) :
    Persistent (typedOK OK X) := by
  unfold typedOK; infer_instance

end defs

end listers
end EtcdGrove
end Perennial
