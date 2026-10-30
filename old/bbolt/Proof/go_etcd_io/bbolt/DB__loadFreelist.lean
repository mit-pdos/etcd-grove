module
public import Spec.go_etcd_io.bbolt.DB__loadFreelist
public import Proof.sync.OnceFresh

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.freelist

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem flpage_flags (pg : List w8) (h : pageFlags pg = freelistPageFlag) :
    (pageOf pg).flags' = W16 16 := by
  simp only [pageOf, h, freelistPageFlag]; rfl

theorem flpage_cnt_nonneg (c : w64) (h : uint.nat c < 2 ^ 62) : 0 ≤ sint.Z c := by word

theorem flpage_cnt (pg : List w8) (hfit : flOff pg + 8 * flN pg ≤ pg.length)
    (hlen : pg.length < 2 ^ 62) : fpOverflow (pageOf pg) → 0 ≤ sint.Z (flPageCount pg) := by
  intro hov
  have : flN pg = uint.nat (flPageCount pg) := by unfold flN fpCount; rw [if_pos hov]
  exact flpage_cnt_nonneg _ (by omega)

theorem flpage_len (pg : List w8) (hfit : flOff pg + 8 * flN pg ≤ pg.length)
    (hlen : pg.length < 2 ^ 62) : (flIds pg).length + FLState.empty.pendingCount < 2 ^ 63 := by
  rw [flIds_length]
  have : FLState.empty.pendingCount = 0 := by
    simp [FLState.pendingCount, FLState.pendingIds, FLState.empty]
  omega

theorem DB.loadFreelist.wp_proof (hNF : newFreelist.spec (GF := GF) (hG := hG))
    (hSync : DB.hasSyncedFreelist.spec (GF := GF) (hG := hG))
    (hMeta : DB.meta.spec (GF := GF) (hG := hG))
    (hFL : Meta.Freelist.spec (GF := GF) (hG := hG))
    (hPage : DB.page.spec (GF := GF) (hG := hG)) :
    DB.loadFreelist.spec (GF := GF) (hG := hG) := by
  intro dbl data m0 m1 st ps ft fl0 dq dqm dq0 dq1 dqd dqs dqp v0 v1 pg hC hft hm0 hm1 hv hsync
    hdata hb hpg
  wp_start as ⟨Honce, Hflf, Hft, Hm0f, Hm1f, Hm0, Hm1, Hd, Hps, Hpg, Hstf, Hst⟩
  wp_auto
  rw [recv_eq_func_mk BAnon BAnon]
  wp_apply (Once.wp_Do_fresh (structFieldRef DB go!"freelistLoad" dbl)
    iprop(db_ptr ↦ dbl ∗ structFieldRef DB go!"freelist" dbl ↦ fl0 ∗
      structFieldRef DB go!"FreelistType" dbl ↦{dq} ft ∗
      structFieldRef DB go!"meta0" dbl ↦{dqm} m0 ∗ structFieldRef DB go!"meta1" dbl ↦{dqm} m1 ∗
      m0 ↦{dq0} v0 ∗ m1 ↦{dq1} v1 ∗
      structFieldRef DB go!"data" dbl ↦{dqd} data ∗ structFieldRef DB go!"pageSize" dbl ↦{dqs} ps ∗
      bytesPointsto (data +ₗ uint.Z ((if metaPick v0 v1 then v1 else v0).freelist' * ps)) dqp pg ∗
      structFieldRef DB go!"stats" dbl ↦{dq} st ∗ (⌜st = null⌝ ∨ ∃ (sv : Stats), st ↦ sv))
    iprop(∃ (a s : Loc) (free : List w64), ⌜PgidsIncr free ∧ free.Perm (flIds pg)⌝ ∗
      structFieldRef DB go!"freelist" dbl ↦ (arrayImpl (GF := GF) a).iface ∗
      ownFL (arrayImpl a) s { FLState.empty with free := free } ∗
      structFieldRef DB go!"FreelistType" dbl ↦{dq} ft ∗
      structFieldRef DB go!"meta0" dbl ↦{dqm} m0 ∗ structFieldRef DB go!"meta1" dbl ↦{dqm} m1 ∗
      m0 ↦{dq0} v0 ∗ m1 ↦{dq1} v1 ∗
      structFieldRef DB go!"data" dbl ↦{dqd} data ∗ structFieldRef DB go!"pageSize" dbl ↦{dqs} ps ∗
      bytesPointsto (data +ₗ uint.Z ((if metaPick v0 v1 then v1 else v0).freelist' * ps)) dqp pg ∗
      structFieldRef DB go!"stats" dbl ↦{dq} st ∗ (⌜st = null⌝ ∨ ∃ (sv : Stats), st ↦ sv)) _)
    $$ [Honce db Hflf Hft Hm0f Hm1f Hm0 Hm1 Hd Hps Hpg Hstf Hst] as HQ
  · iframe
    imodintro
    iintro %Φ' ⟨db, Hflf, Hft, Hm0f, Hm1f, Hm0, Hm1, Hd, Hps, Hpg, Hstf, Hst⟩ HΦ'
    wp_auto
    wp_apply hNF ft hft as %a %s Hfl
    try wp_auto
    wp_apply hSync dbl m0 m1 dqm dq0 dq1 v0 v1 hm0 hm1 hv $$ [Hm0f Hm1f Hm0 Hm1]
      as ⟨Hm0f, Hm1f, Hm0, Hm1⟩
    · iframe
    rw [decide_eq_false hsync]
    try wp_auto
    wp_apply hMeta dbl m0 m1 dqm dq0 dq1 v0 v1 hm0 hm1 hv $$ [Hm0f Hm1f Hm0 Hm1]
      as ⟨%hmv, Hm0f, Hm1f, Hm0, Hm1⟩
    · iframe
    try wp_auto
    -- the current meta's freelist page
    ihave Hcm : (if metaPick v0 v1 then m1 else m0) ↦{if metaPick v0 v1 then dq1 else dq0}
        (if metaPick v0 v1 then v1 else v0) ∗
      ((if metaPick v0 v1 then m1 else m0) ↦{if metaPick v0 v1 then dq1 else dq0}
        (if metaPick v0 v1 then v1 else v0) -∗ m0 ↦{dq0} v0 ∗ m1 ↦{dq1} v1) $$ [Hm0 Hm1]
    · cases metaPick v0 v1
      · simp only [Bool.false_eq_true, ↓reduceIte]; iframe; iintro H; iframe
      · simp only [↓reduceIte]; iframe; iintro H; iframe
    icases Hcm with ⟨Hcm, Hcmb⟩
    ihave #Hcpkg : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common) $$ []
    · iPkgInit
    wp_apply hFL _ _ _ $$ [Hcm] as Hcm
    · iframe
    ihave Hms := Hcmb $$ Hcm
    icases Hms with ⟨Hm0, Hm1⟩
    try wp_auto
    wp_apply hPage dbl data ps dqd dqs _ hdata hb $$ [Hd Hps] as ⟨Hd, Hps⟩
    · iframe
    try wp_auto
    -- `Read`: the page's header, overflow count and ids
    obtain ⟨hfl, hfit, hlen, hnd, h2⟩ := hpg
    have hcar : (data +ₗ uint.Z ((if metaPick v0 v1 then v1 else v0).freelist' * ps)).locCar ≠ 0 := by
      simpa [Loc.add] using hdata
    icases (flpage_bytes _ dqp pg hcar hfit hlen).1 $$ Hpg with ⟨Hpv, Hcnt, Hids, Hrest⟩
    ihave #Hflpkg : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist) $$ []
    · iPkgInit
    have hR := (hC a).read
    unfold FLImpl.ReadSpec at hR
    simp only [arrayImpl] at hR
    wp_apply hR s FLState.empty _ (pageOf pg) dqp (flPageCount pg) (flIds pg) dqp hcar
      (flpage_flags pg hfl) (flpage_cnt pg hfit hlen) hnd
      (fun x hx => ⟨h2 x hx, by simp [FLState.pendingIds, FLState.empty]⟩)
      (flpage_len pg hfit hlen) (Or.inr rfl) $$ [Hfl Hpv Hcnt Hids] as %free ⟨%hfree, Hfl, Hpv, Hcnt, Hids⟩
    · iframe
    ihave Hpg := (flpage_bytes _ dqp pg hcar hfit hlen).2 $$ [Hpv Hcnt Hids Hrest]
    · iframe
    try wp_auto
    -- the statistics' free count
    icases Hst with (%Hsn | ⟨%sv, Hsv⟩)
    · rw [decide_eq_true Hsn]
      try wp_auto
      iapply HΦ'
      iexists a, s, free
      isplitr
      · ipureintro; exact hfree
      iframe
      ileft; ipureintro; exact Hsn
    · icases typedPointsto_not_null_dup _ _ _ $$ Hsv with ⟨Hsv, %Hsnn⟩
      rw [decide_eq_false Hsnn]
      try wp_auto
      have hF := (hC a).freeCount
      unfold FLImpl.IfaceFreeCountSpec at hF
      simp only [arrayImpl] at hF
      wp_apply hF s _ $$ [Hfl] as Hfl
      · iframe
      try wp_auto
      iapply HΦ'
      iexists a, s, free
      isplitr
      · ipureintro; exact hfree
      iframe
      try (iright; iexists _; iframe)
  try wp_auto
  iapply HΦ
  iexact HQ

end proof

end bbolt
end EtcdGrove
end Perennial
