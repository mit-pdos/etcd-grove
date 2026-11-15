/-
The `*hashMap` freelist implementation meets `FLImpl.Contract` (the methods `shared` calls
back: `FreeCount`, `freePageIds`, `Init`, `mergeSpans`) and `FLImpl.AllocateSpec` (U2).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.hashMap.hashMap__Allocate
public import Proof.go_etcd_io.bbolt.internal.freelist.Impl.hashMap.hashMap__mergeSpans

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace internal
namespace freelist

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- The hash map's `FreeCount` meets the contract's spec. -/
theorem hashImpl_freeCount (hVerify : _root_.Perennial.EtcdGrove.bbolt.internal.common.Verify.spec (GF := GF) (hG := hG)) (h : Loc) :
    (hashImpl (GF := GF) h).FreeCountSpec := by
  unfold FLImpl.FreeCountSpec
  rw [hashImpl_ity, hashImpl_iv]
  intro free
  iintro %Φ ⟨#Hpkg, Hown⟩ HΦ
  iapply (hashMap.FreeCount.wp_proof hVerify hashMap.hashmapFreeCountSlow.wp_proof h h free)
    $$ [Hown]
  · iframe Hpkg; iapply (ownHashPart_iff h h free).2 $$ Hown
  inext
  iintro Hown
  iapply HΦ
  iapply (ownHashPart_iff h h free).1 $$ Hown

/-- The hash map's `mergeSpans` meets the contract's spec. -/
theorem hashImpl_mergeSpans (hdel : PidSetDeleteUnfold (GF := GF))
    (hVerify : _root_.Perennial.EtcdGrove.bbolt.internal.common.Verify.spec (GF := GF) (hG := hG))
    (hDeep : _root_.Perennial.EtcdGrove.reflect.DeepEqual.spec_pgidSet (GF := GF) (hG := hG)) (h : Loc) :
    (hashImpl (GF := GF) h).MergeSpansSpec := by
  unfold FLImpl.MergeSpansSpec
  rw [hashImpl_ity, hashImpl_iv]
  intro free ids ys _ hnd hfge hge hlen
  iintro %Φ ⟨#Hpkg, Hown, Hys, Hcap⟩ HΦ
  iapply (hashMap.mergeSpans.wp_proof hVerify hashMap.idsFromFreemaps.wp_proof
    hashMap.idsFromForwardMap.wp_proof hashMap.idsFromBackwardMap.wp_proof hDeep
    (hashMap.mergeWithExistingSpan.wp_proof (hashMap.delSpan.wp_proof hdel)
      hashMap.addSpan.wp_proof) h h free ids ys hnd hfge hge hlen) $$ [Hown Hys Hcap]
  · iframe Hpkg Hys Hcap; iapply (ownHashPart_iff h h free).2 $$ Hown
  inext
  iintro Hown
  iapply HΦ
  iapply (ownHashPart_iff h h _).1 $$ Hown

/-- **The `*hashMap` meets the contract** (given `delete`'s semantics at `pidSet`,
`Lemmas/HashDelete.lean`, a Perennial gap). -/
theorem hashImpl_contract (hdel : PidSetDeleteUnfold (GF := GF))
    (hVerify : _root_.Perennial.EtcdGrove.bbolt.internal.common.Verify.spec (GF := GF) (hG := hG))
    (hSorted : _root_.Perennial.EtcdGrove.sort.SliceIsSorted.spec (GF := GF) (hG := hG))
    (hDeep : _root_.Perennial.EtcdGrove.reflect.DeepEqual.spec_pgidSet (GF := GF) (hG := hG))
    (a : Loc) : (hashImpl (GF := GF) a).Contract where
  freeCount := hashImpl_freeCount hVerify a
  freePageIds := hashImpl_freePageIds
    (hashMap.freePageIds.wp_proof
      (hashMap.FreeCount.wp_proof hVerify hashMap.hashmapFreeCountSlow.wp_proof)) a
  init := hashMap.Init.wp_proof hSorted hashMap.addSpan.wp_proof
    (hashMap.freePageIds.wp_proof
      (hashMap.FreeCount.wp_proof hVerify hashMap.hashmapFreeCountSlow.wp_proof)) a
  mergeSpans := hashImpl_mergeSpans hdel hVerify hDeep a

/-- **The `*hashMap`'s `Allocate`** (given `delete`'s semantics at `pidSet`). -/
theorem hashImpl_allocate (hdel : PidSetDeleteUnfold (GF := GF)) (a : Loc) :
    (hashImpl (GF := GF) a).AllocateSpec :=
  hashMap.Allocate.wp_proof (hashMap.delSpan.wp_proof hdel) hashMap.addSpan.wp_proof a

end proof

end freelist
end internal
end bbolt
end EtcdGrove
end Perennial
