/-
Proof of `Spec/k8s_io/apiserver/pkg/storage/cacher/Cacher__get.lean`. Lean-first (no Rocq
counterpart).

`WaitUntilFreshAndGet`'s read; the snapshot's element of the key (`ownStore_lookup`: a published
snapshot's elements are `isElem`), so the type assertion holds and the object is its element's.

Not linked (`etc/link-lean-first-cacher.txt`): the spec's points-to of `Cacher`'s `watchCache`
field rests on `Cacher`'s generated instances, `sorry -- axiomatized type` (Goose axiomatizes the
type: some of its fields' types are not translated), which no linked result may reach.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.cacher.Cacher__get
public import Spec.k8s_io.apiserver.pkg.storage.cacher.watchCache__WaitUntilFreshAndGet

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cacher

open Iris Iris.BI Iris.ProofMode k8s_io.apiserver.pkg.storage.cacher

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.cacher.Assumptions]
variable [btree_sem : k8s_io.utils.third_party.forked.golang.btree.Assumptions]
variable [store_sem : k8s_io.apiserver.pkg.storage.cacher.store.Assumptions]

theorem Cacher.get.wp_proof
    (wp_WaitUntilFreshAndGet : watchCache.WaitUntilFreshAndGet.spec (GF := GF) (hG := hG)) :
    Cacher.get.spec (GF := GF) (hG := hG) := by
  intro cp wc γ Ψ parseRV ctxPre curRV ctx key rvs
  wp_start as ⟨#Hwcf, #Hwc, #Hget, Hcp, Htok⟩
  (try wp_auto)
  wp_apply (wp_WaitUntilFreshAndGet wc γ Ψ parseRV ctxPre curRV ctx rvs key) $$ [Hcp Htok]
    as %obj %ex %rv %err ⟨Htok, Hres⟩
  · iframe #; iframe
  (try wp_auto)
  cases err with
  | ok ei =>
    (try wp_auto)
    iapply HΦ
    iframe Htok
    iintro %h
    exfalso; simp_all
  | nil =>
    ispecialize Hres $$ %rfl
    icases Hres with ⟨%p, %st, %m, %Hv, Hm, #Hsn, #HΨ⟩
    obtain ⟨rfl, rfl, rfl, Hge⟩ := Hv
    ihave #Hsn' := Hsn
    iunfold isSnap at Hsn'
    icases (ownStore_lookup p DFrac.discard st.1 st.2 key) $$ Hsn' with ⟨-, Hlk⟩
    iunfold lookupFact at Hlk
    unfold lookupElem
    cases hl : btree.lookup st.1 key with
    | none =>
      simp only [Option.getD_none, Option.isSome_none]
      (try wp_auto)
      iapply HΦ
      iframe Htok
      iintro -
      iexists p, st, m
      iframe Hsn HΨ Hm
      rw [hl]
      ipureintro
      exact ⟨⟨rfl, Hge⟩, rfl⟩
    | some e =>
      simp only [Option.getD_some, Option.isSome_some]
      iunfold isElem at Hlk
      icases Hlk with ⟨%el, #Hel, %Hk⟩
      ihave Hel' := Hel
      iStructNamed Hel'
      (try wp_auto)
      iapply HΦ
      iframe Htok
      iintro -
      iexists p, st, m
      iframe Hsn HΨ Hm
      rw [hl]
      isplitr
      · ipureintro; exact ⟨rfl, Hge⟩
      iexists el
      iframe Hel
      ipureintro
      exact ⟨rfl, rfl, Hk⟩

end proof

end cacher
end EtcdGrove
end Perennial
