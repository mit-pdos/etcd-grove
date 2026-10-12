/-
Proof of `Spec/store__Get.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.store__Get
public import Spec.go_etcd_io.etcd.cache.v3.store__getSnapshot
public import Spec.go_etcd_io.etcd.cache.v3.snapshot__Range

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem store.Get.wp_proof
    (wp_getSnapshot : store.getSnapshot.spec (GF := GF) (hG := hG))
    (wp_Range : snapshot.Range.spec (GF := GF) (hG := hG)) :
    store.Get.spec (GF := GF) (hG := hG) := by
  intro s γ cap E R r0 startSl endSl startKey endKey d1 d2 rev
  wp_start as ⟨#HS, Hrd, #Hlb, Hs, He⟩
  ihave Hci : (cacheInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  ihave #Hrpc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
  · iPkgInit
  ihave Hri : (rpctypesInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hrpc
  icases Hci with ⟨⟨%eNR, #HeNR⟩, -, -, -⟩
  icases Hri with ⟨⟨%eFR, #HeFR⟩, ⟨%eCP, #HeCP, -⟩, -⟩
  wp_auto
  wp_apply wp_getSnapshot $$ [$HS $Hrd $Hlb] as %p %lrev %err ⟨Hrd, %st, Hseen, #HR, #Herr, Hres⟩
  generalize Hm : snapModel st rev = res
  cases res with
  | ok r m =>
    simp only [snapErr]
    icases Herr with %Herr
    icases Hres with ⟨%Hlrev, #Hp⟩
    iunfold snapCert at Hp
    icases Hp with ⟨#Hp, #HE⟩
    subst Herr
    wp_auto
    wp_apply wp_Range $$ [$Hp $Hs $He] as %out ⟨Hs, He, Hout, Hcap, #Hkvs⟩
    iapply HΦ
    iframe Hrd Hs He
    iexists st
    rw [Hm]
    dsimp only
    iframe Hseen HR Hout Hcap Hkvs HE
    ipureintro; exact ⟨rfl, Hlrev⟩
  | notReady =>
    simp only [snapErr]
    icombine Herr HeNR gives %Heq
    subst Heq
    wp_auto
    iapply HΦ
    iframe Hrd Hs He
    iexists st
    rw [Hm]
    iframe Hseen HR
    iframe HeNR
    ipureintro; exact ⟨rfl, rfl⟩
  | invalid =>
    simp only [snapErr]
    icases Herr with % ⟨e, rfl⟩
    wp_auto
    iapply HΦ
    iframe Hrd Hs He
    iexists st
    rw [Hm]
    iframe Hseen HR
    ipureintro; exact ⟨⟨e, rfl⟩, rfl, rfl⟩
  | future =>
    simp only [snapErr]
    icombine Herr HeFR gives %Heq
    subst Heq
    wp_auto
    iapply HΦ
    iframe Hrd Hs He
    iexists st
    rw [Hm]
    iframe Hseen HR
    iframe HeFR
    ipureintro; exact ⟨rfl, rfl⟩
  | compacted =>
    simp only [snapErr]
    icombine Herr HeCP gives %Heq
    subst Heq
    wp_auto
    iapply HΦ
    iframe Hrd Hs He
    iexists st
    rw [Hm]
    iframe Hseen HR
    iframe HeCP
    ipureintro; exact ⟨rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
