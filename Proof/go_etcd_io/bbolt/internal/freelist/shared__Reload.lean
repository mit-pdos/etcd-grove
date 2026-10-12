module
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__Reload
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__NoSyncReload

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

theorem shared.Reload.wp_proof (hRead : shared.Read.spec (GF := GF) (hG := hG))
    (hNSR : shared.NoSyncReload.spec (GF := GF) (hG := hG)) :
    shared.Reload.spec (GF := GF) (hG := hG) := by
  intro I s σ p pv dq c xs dq2 hInit hFPI Hnn Hfl Hov Hnd Hxs Hlen
  wp_start as ⟨#Hhdl, Hsh, Hown, Hp, Hcc, Hsl⟩
  wp_auto
  wp_apply (hRead I s σ p pv dq c xs dq2 hInit Hnn Hfl Hov Hnd Hxs Hlen)
    $$ [Hsh Hown Hp Hcc Hsl] as %fr ⟨%Hfr, Hsh, Hown, Hp, Hcc, Hsl⟩
  · iframe
    try iexact Hhdl
  try wp_auto
  icases ownShared_wf _ _ _ $$ Hsh with ⟨Hsh, %Hwf'⟩
  iunfold ownShared, ownSharedC at Hsh
  icases Hsh with ⟨%sv, %c', Hsh, %Hok⟩
  iNamed Hsh
  wp_method_call
  wp_call
  try wp_auto
  rw [Hiface]
  unfold FLImpl.iface
  try wp_auto
  wp_bind (App (Val #(methods I.ity go!"freePageIds" I.iv)) (Val #()))
  iapply (hFPI s fr) $$ Hown
  inext
  iintro %r ⟨Hr, Hback⟩
  ihave Hsh : ownShared s I.iface { σ with free := fr } $$ [Hs Hro Hro_cap Hallocs Hcache Hpending Hpds]
  · unfold ownShared ownSharedC
    iexists sv, c'
    iframe
    ipureintro; exact ⟨Hiface, Hok⟩
  try wp_auto
  have Hnp : ∀ x ∈ fr, x ∉ σ.pendingIds := fun x hx => (Hxs x (Hfr.2.mem_iff.1 hx)).2
  have Hfilt : fr.filter (fun x => decide (x ∉ σ.pendingIds)) = fr :=
    List.filter_eq_self.2 (fun x hx => by simpa using Hnp x hx)
  wp_apply (hNSR I s { σ with free := fr } r fr (DFrac.own 1) iprop(True) hInit Hfr.1
    (fun x hx => (Hxs x (Hfr.2.mem_iff.1 hx)).1) (by rw [Hfr.2.length_eq]; exact Hlen))
    $$ [Hsh Hr Hback] as ⟨Hsh, Hown, -⟩
  · iframe
    isplitl []
    · iexact Hhdl
    iintro Hr
    ihave Hown := Hback $$ Hr
    iframe
  try wp_auto
  have Hfilt' : fr.filter (fun x => !decide (x ∈ ({ σ with free := fr } : FLState).pendingIds)) = fr :=
    List.filter_eq_self.2 (fun x hx => by
      have : x ∉ ({ σ with free := fr } : FLState).pendingIds := Hnp x hx
      simpa using this)
  rw [Hfilt']
  iapply HΦ
  iframe
  isplitr
  · ipureintro; exact Hfr
  iExactEq Hsh; rfl

end proof

end bbolt
end EtcdGrove
end Perennial
