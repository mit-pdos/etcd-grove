/-
`reconcileReplacement(logger, nil, store, newItems, keyOf, onDelete, onReplace)`
(`the_real_fifo.go:619`), as `processReplacedAllInfo` calls it (no queued items): `onDelete` with a
tombstone for each of the store's keys the new items lack, then `onReplace` on each new item.
Lean-first.
-/
module

public import Proof.k8s_io.client_go.tools.cache.InformerDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI k8s_io.client_go.tools.cache

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- The keys a replacement by `objs` (keyed by `KF`) deletes from the items `it`, each once. -/
def delKeys (KF : GoInterface → GoString) (it : Items) (objs : List GoInterface)
    (dks : List GoString) : Prop :=
  dks.Nodup ∧ ∀ k, k ∈ dks ↔ k ∈ it ∧ k ∉ objs.map KF

/-- **`reconcileReplacement(lg, nil, ca, nsl, kf', od, orp)`**, the store `ca` (a
`KeyListerGetter`) held by its exclusive writer at `σ` (`SW σ`, lent to `orp` and given back
unchanged), the new items `objs` keyed by `kf'` (`KF`, no error): `od` on the tombstone of each
store key the new items lack (`delKeys`, in some order), then `orp` on each new item in order. -/
abbrev reconcileReplacement.spec : Prop :=
  ∀ (lg : github_com.go_logr.logr.Logger) (ca ts : Loc) (γ : TsNames) (OK : GoInterface → IProp GF) (Fam : Nat → Fn)
    (kf kf' : GoFunc) (KF : GoInterface → GoString) (SW : St → IProp GF) (σ : St)
    (nsl : GoSlice) (dq : DFrac) (objs : List GoInterface) (od orp : GoFunc)
    (Dl : List GoInterface → IProp GF) (Rl : List GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache ∗ isCache ca ts γ OK Fam kf ∗
      tsReader ts γ OK Fam ∗ storeWriter γ SW ∗ SW σ ∗ nsl ↦*{dq} objs ∗
      keyOk (fun x => iprop(⌜x ∈ objs⌝)) kf' KF ∗ Dl [] ∗ Rl [] ∗
      □ (∀ (ds : List GoInterface) (k : GoString) (x : GoInterface), {{ Dl ds ∗ okNil OK x }}
          (App (Val #od) (Val #(DeletedFinalStateUnknown.mk k x)))
          {{ RET #interface.nil; Dl (ds ++ [tombstone k x]) }}) ∗
      □ (∀ (rs : List GoInterface) (o : GoInterface), {{ Rl rs ∗ SW σ ∗ tsReader ts γ OK Fam ∗ ⌜o ∈ objs⌝ }}
          (App (Val #orp) (Val #o))
          {{ RET #interface.nil; Rl (rs ++ [o]) ∗ SW σ ∗ tsReader ts γ OK Fam }}) }}
    (App (App (App (App (App (App (App (Val (@! reconcileReplacement)) (Val #lg))
      (Val #slice.nil))
      (Val #(interface.mkOk (go.GoType.PointerType k8s_io.client_go.tools.cache.cache.ty) #ca)))
      (Val #nsl)) (Val #kf')) (Val #od)) (Val #orp))
  {{ RET #interface.nil; ∃ dks : List GoString, ⌜delKeys KF σ.items objs dks⌝ ∗
      Dl (dks.map (fun k => tombstone k (objAt σ.items k))) ∗ Rl objs ∗ SW σ ∗
      nsl ↦*{dq} objs ∗ tsReader ts γ OK Fam }}

end spec

end cache
end EtcdGrove
end Perennial
