/-
`(*Cacher).get(ctx, key, resourceVersion)` (`cacher.go`), the cacher's read of an object from the
watch cache (`Cacher.Get`'s; KEP-6404, `notes/kep-6404-plan.md`): `WaitUntilFreshAndGet`'s
read, its element's object. Without an error, the key's object in a state `st` the store
published (with the caller's fact `Ψ st`), at the version `WaitUntilFreshAndGet` waits for or
later, and `st`'s version: `exists` false if the key is not in `st`, otherwise the object of its
element. Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.cacher.DefsWC

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cacher

open Iris Iris.BI k8s_io.apiserver.pkg.storage.cacher

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.cacher.Assumptions]
variable [btree_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]

/-- See the file header. -/
abbrev Cacher.get.spec : Prop :=
  ∀ (cp wc : Loc) (γ : WCSNames) (Ψ : SnapSt → IProp GF) (parseRV : GoString → Option w64)
    (ctxPre : GoInterface → IProp GF) (curRV : w64 → IProp GF) (ctx : GoInterface)
    (key rvs : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.cacher ∗
      structFieldRef Cacher go!"watchCache" cp ↦□ wc ∗ isWC wc γ Ψ ∗
      wcGetOk wc parseRV ctxPre curRV ∗ ctxPre ctx ∗
      sync.ownRWMutex (structFieldRef watchCache go!"RWMutex" wc) (wcLockP wc γ) }}
    (App (App (App (Val (cp @!! go.GoType.PointerType Cacher.ty @!! go!"get")) (Val #ctx))
      (Val #key)) (Val #rvs))
  {{ (obj : GoInterface) (ex : Bool) (rv : w64) (err : GoInterface),
      RET (PairV (PairV (PairV #obj #ex) #rv) #err);
      sync.ownRWMutex (structFieldRef watchCache go!"RWMutex" wc) (wcLockP wc γ) ∗
      (⌜err = GoInterface.nil⌝ -∗ ∃ (p : Loc) (st : SnapSt) (m : w64),
        ⌜rv = st.2 ∧ uint.Z m ≤ uint.Z st.2⌝ ∗
        (⌜rvs = go!""⌝ ∗ curRV m ∨ ⌜rvs ≠ go!"" ∧ parseRV rvs = some m⌝) ∗
        isSnap p st.1 st.2 ∗ □ Ψ st ∗
        match btree.lookup st.1 key with
        | none => ⌜ex = false⌝
        | some e => ∃ el : k8s_io.apiserver.pkg.storage.cacher.store.Element,
            ⌜ex = true ∧ obj = el.Object' ∧ el.Key' = key⌝ ∗ e ↦□ el) }}

end spec

end cacher
end EtcdGrove
end Perennial
