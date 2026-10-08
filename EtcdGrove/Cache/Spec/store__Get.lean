/-
`store.Get(startKey, endKey, rev)`. Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
import EtcdGrove.Cache.InvStore

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `s.Get(startKey, endKey, rev)`: for some state `st` of the store (at least the caller's
lower bound `r0`, `storeSeen`), what `snapModel st rev` says: the key-values of the
snapshot's map in `kvRange startKey endKey` (in key order, an owned slice of read-only
`*KeyValue`s) and `st`'s latest revision, or `nil`, `0` and the error (`snapErr`). -/
abbrev store.Get.spec : Prop :=
  ∀ (s : Loc) (γ : StoreNames) (cap : Nat) (r0 : w64) (startSl endSl : GoSlice)
    (startKey endKey : GoString) (d1 d2 : DFrac) (rev : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      isStore s γ cap ∗ storeReader s γ cap ∗ storeRevLb γ r0 ∗
      startSl ↦*{d1} startKey ∗ endSl ↦*{d2} endKey }}
    (App (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"Get")) (Val #startSl)) (Val #endSl)) (Val #rev))
  {{ (kvs : GoSlice) (lrev : w64) (err : GoInterface), RET (PairV (PairV #kvs #lrev) #err);
      storeReader s γ cap ∗ startSl ↦*{d1} startKey ∗ endSl ↦*{d2} endKey ∗
      ∃ st : StoreState, storeSeen γ cap r0 st ∗ snapErr (snapModel st rev) err ∗
        match snapModel st rev with
        | .ok _ m => ⌜lrev = st.latestRev⌝ ∗
            kvs ↦* ((kvRange startKey endKey m).map Prod.snd) ∗
            ownSliceCap Loc kvs (DFrac.own 1) ∗ kvsAt (kvRange startKey endKey m)
        | _ => ⌜kvs = slice.nil ∧ lrev = W64 0⌝ }}

end spec

end EtcdGrove
end Perennial
