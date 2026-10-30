module
public import Spec.go_etcd_io.bbolt.Bucket__free_x
public import Spec.go_etcd_io.bbolt.Bucket__forEachPageNode_x
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__RootPage
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__SetRootPage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem ib_root0 (ib : InBucket) (h : ib.root' = W64 0) :
    ({ ib with root' := W64 0 } : InBucket) = ib := by
  cases ib; simp only at h; subst h; rfl

theorem nv_pgid0 (nv : node) (h : nv.pgid' = W64 0) : ({ nv with pgid' := W64 0 } : node) = nv := by
  cases nv; simp only at h; subst h; rfl

theorem Bucket.free.wp_xproof (hRoot : InBucket.RootPage.spec (GF := GF) (hG := hG))
    (hfe : Bucket.forEachPageNode.xspec (GF := GF) (hG := hG))
    (hnf : node.free.xspec (GF := GF) (hG := hG))
    (hSet : InBucket.SetRootPage.spec (GF := GF) (hG := hG)) :
    Bucket.free.xspec (GF := GF) (hG := hG) := by
  intro I γd γ W hwm txl txid ρ bl B pmap pm mp mv dqt F nv hFree HvOK Htx Hmtx HF Hrn Hbl Hleaf
    Hr0 Hroot Hcar
  wp_start as ⟨Hb, Hib, Hnm, Hn, Hv, Hpf, Hpm, Hdb, Hmf, Hmv, Hdbw, HFt, Htok⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  wp_auto
  wp_method_call
  try wp_auto
  wp_apply hRoot $$ [Hib] as Hib
  · iframe
  try wp_auto
  by_cases h0 : B.ib.root' = W64 0
  · rw [decide_eq_true h0]
    try wp_auto
    iapply HΦ
    iexists ρ, F
    rw [ib_root0 B.ib h0, nv_pgid0 nv (Hr0 h0)]
    iframe
    ipureintro
    exact ⟨HF, ⟨ρ.fl, rfl⟩, fun _ => ⟨rfl, rfl, Hr0 h0⟩, fun h => absurd h0 h⟩
  rw [decide_eq_false h0]
  try wp_auto
  wp_func_lits
  obtain ⟨Hpg, Hres, Hnn, Hpgid, Hwf, Hpmn⟩ := Hroot h0
  rw [if_neg h0]
  wp_apply (hfe W bl B.bv B (DFrac.own 1) txl pmap pm dqt _ B.bv.rootNode'
      iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ tx_ptr ↦ B.bv.tx' ∗ B.bv.rootNode' ↦ nv ∗ structFieldRef Tx go!"meta" txl ↦{dqt} mp ∗
        mp ↦ mv ∗ dbWR I γd W txl txid ρ ∗ pgToks γ F ∗ (uint.nat B.ib.root' ↪[γ] () : IProp GF))
      (fun nv' => iprop(∃ (ρ' : DBState) (F' : GMap Nat (List w8)),
        ⌜nv' = ({ nv with pgid' := W64 0 } : node)⌝ ∗ tx_ptr ↦ B.bv.tx' ∗
        structFieldRef Tx go!"meta" txl ↦{dqt} mp ∗ mp ↦ mv ∗ dbWR I γd W txl txid ρ' ∗
        pgToks γ F' ∗
        ⌜freedOK W ρ'.fl txid F' ∧ (∃ fl, ρ' = { ρ with fl := fl }) ∧
          ∃ pg, W.pages !! uint.nat B.ib.root' = some pg ∧
            F' = <[uint.nat B.ib.root' := pg]> F ∧
            ρ'.fl = ρ.fl.freePages txid B.ib.root' (1 + pageOverflow pg)⌝))
      rfl Htx Hnn Hpg h0 Hres Hcar HvOK.2.2.1 ?Hfn)
    $$ [Hb Hib Hnm Hv Hpf Hpm Hdb tx Hn Hmf Hmv Hdbw HFt Htok Hpkg]
    as ⟨Hb, Hib, Hnm, Hv, Hpf, Hpm, Hdb, %nv', Hn, %Hl, ⟨%ρ', %F', %Hnv', Htxp, Hmf, Hmv, Hdbw, HFt, %Hfacts⟩⟩
  case Hfn =>
    iintro %Φ' ⟨⟨#Hpkg, Htxp, Hn, Hmf, Hmv, Hdbw, HFt, Htok⟩, Hb, Hv, Hpf, Hpm, Hdb⟩ HΦ'
    wp_auto
    have h0' : nv.pgid' ≠ W64 0 := by rw [Hpgid]; exact h0
    wp_apply hnf I γd γ W hwm txl txid ρ bl B.bv (DFrac.own 1) pmap pm mp mv dqt F
        B.bv.rootNode' nv hFree HvOK Htx Hbl Hmtx HF (fun _ => ⟨by rw [Hpgid]; exact Hwf, by rw [Hpgid]; exact Hpmn⟩)
      $$ [Hn Hb Hv Hpf Hpm Hdb Hmf Hmv Hdbw HFt Htok]
      as ⟨%ρ', %F', Hn, Hb, Hv, Hpf, Hpm, Hdb, Hmf, Hmv, Hdbw, HFt, %Hfr⟩
    · rw [if_neg h0', Hpgid]; iframe
    try wp_auto
    iapply HΦ'
    iexists _
    isplitl [Hn]
    · iexact Hn
    isplitr
    · ipureintro; exact Hleaf
    iframe
    isplitr
    · ipureintro; rfl
    ipureintro
    obtain ⟨h1, h2, -, h4⟩ := Hfr
    obtain ⟨pg, hpg, hF, hfl⟩ := h4 h0'
    refine ⟨h1, h2, pg, ?_, ?_, ?_⟩
    · rw [← Hpgid]; exact hpg
    · rw [← Hpgid]; exact hF
    · rw [hfl, ← Hpgid]; congr 1; unfold uint.nat; word
  · iframe; iexact Hpkg
  try wp_auto
  wp_method_call
  try wp_auto
  wp_apply hSet $$ [Hib] as Hib
  · iframe
  try wp_auto
  iapply HΦ
  iexists ρ', F'
  rw [← Hnv']
  iframe
  ipureintro
  obtain ⟨h1, h2, h3⟩ := Hfacts
  exact ⟨h1, h2, fun h => absurd h h0, fun _ => h3⟩

end proof

end bbolt
end EtcdGrove
end Perennial
