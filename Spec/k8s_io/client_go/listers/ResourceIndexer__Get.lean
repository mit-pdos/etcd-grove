/-
`ResourceIndexer[T].Get(name)` (`generic_helpers.go:57`): the object of the lister's namespace and
`name` in the store, or a NotFound error. Lean-first.
-/
module

public import Proof.k8s_io.client_go.listers.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace listers

open Iris Iris.BI cache k8s_io.client_go.listers

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.listers.Assumptions]

/-- What `Get` returns at the store's state `σ`: the item at the key, a `*X`, and no error; or, if
there is none, `nil` and an error. -/
def getPost (OK : GoInterface → IProp GF) (X : go.GoType) (σ : St) (key : GoString) (r : Loc)
    (err : GoInterface) : IProp GF :=
  match σ.items !! key with
  | some o => iprop(⌜o = ptrObj X r ∧ err = interface.nil⌝ ∗ □ OK o)
  | none => iprop(⌜r = null ∧ err ≠ interface.nil⌝)

/-- **`l.Get(name)`** for the lister `l` over the cache `ca` (`riVal ca res ns`), logically atomic
(a reader), for a store whose objects are `*X` (`typedOK`) and has no `nil` item: the item at
`nsKey ns name` at the linearization point (`getPost`). -/
abbrev ResourceIndexer.Get.spec : Prop :=
  ∀ (X : go.GoType) (ca ts : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn GF)
    (kf : GoFunc) (res : k8s_io.apimachinery.pkg.runtime.schema.GroupResource) (ns name : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.listers ∗ isCache ca ts γ OK Fam kf ∗
      tsReader ts γ OK Fam ∗ typedOK OK X }}
  <<{ ∀∀ σ, storeSt γ σ ∗ ⌜noNil σ.items⌝ }>>
    (App (Val #(methods (ResourceIndexer.ty (go.GoType.PointerType X)) go!"Get"
      #(riVal ca res ns))) (Val #name))
    @@ ∅
  <<{ storeSt γ σ ∗ ⌜noNil σ.items⌝ }>>
  {{ (r : Loc) (err : GoInterface), RET (PairV #r #err);
      getPost OK X σ (nsKey ns name) r err ∗ tsReader ts γ OK Fam }}

end spec

end listers
end EtcdGrove
end Perennial
