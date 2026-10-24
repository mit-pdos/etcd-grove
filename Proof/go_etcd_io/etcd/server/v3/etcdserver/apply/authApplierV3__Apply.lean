/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.authApplierV3__Apply
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.needAdminPermission
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Packaging

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.authApplierV3.Apply.wp_proof
    (hNA : apply.needAdminPermission.spec (GF := GF) (hG := hG)) :
    apply.authApplierV3.Apply.spec (GF := GF) (hG := hG) := by
  intro E c inner p r rq skip v3 af A B
  wp_start as ⟨#Hauth, #Hinner, #Hw, HA, #Haf⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold apply.authIs at Hauth
  icases Hauth with ⟨#Happ, ⟨%st, #Hasf, #Hst⟩, -, #Hmu⟩
  ihave #Hst' := Hst
  iunfold apply.isAuthStore at Hst'
  icases Hst' with ⟨%sti, %Hsti, -, -, -, #HAdmin, -⟩
  subst Hsti
  ihave #Hin := Hinner
  iunfold apply.applierSpec at Hin
  icases Hin with ⟨%bi, %Hbi, #Ht⟩
  subst Hbi
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨-, -, -, -, -, -, -, -, -, #HApplyI⟩
  ihave #Hw' := Hw
  iunfold apply.irrWrapperIs at Hw'
  icases Hw' with ⟨%Hrn, %ip, #Hip, #Hirr, #Hskip⟩
  ihave #Hirr' := Hirr
  iunfold apply.internalRaftRequestIs at Hirr'
  icases Hirr' with ⟨%Hipn, -, ⟨%hl, #HH, #Hhdr⟩, -⟩
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinfo, Hard⟩
  iunfold apply.authInfoIdle at Hinfo
  wp_join iprop(structFieldRef authApplierV3 go!"authInfo" p ↦ apply.principalOf rq ∗ aa_ptr ↦ p ∗
      r_ptr ↦ r)
    at (if: _ then _ else _) with [Hinfo aa r] as ⟨Hinfo, aa, r⟩
  · -- the header's principal: with a header its fields, else the zero `AuthInfo`
    cases hh : rq.header with
    | none =>
      have hp : apply.principalOf rq = zeroValDef := by simp [apply.principalOf, hh]
      simp only [apply.optReqIs]
      icases Hhdr with %Hnull
      wp_if_destruct
      · (try wp_auto)
        rw [hp]
        wp_join_done
        (try iframe)
      · exact absurd Hnull Hif
    | some hm =>
      have hp : apply.principalOf rq = ⟨hm.username, hm.authRevision⟩ := by
        simp [apply.principalOf, hh]
      simp only [apply.optReqIs]
      iunfold apply.headerIs at Hhdr
      icases Hhdr with ⟨%Hhn, -, #HU, #HR⟩
      wp_if_destruct
      · exact absurd rfl Hhn
      · (try wp_auto)
        rw [hp]
        isplitr
        · ipureintro; first | rfl | trivial
        iframe aa r
        iExactEq Hinfo
        rfl
  wp_apply (hNA ip rq) $$ [$Hirr] as %b %Hb
  subst Hb
  cases hna : apply.needAdminPermission rq
  · -- no admin check
    wp_auto
    wp_apply HApplyI $$ %r %rq %skip %v3 %af
        %(iprop(A ∗ structFieldRef authApplierV3 go!"authInfo" p ↦ apply.principalOf rq))
        %(fun ar => iprop(B ar ∗ ∃ i : go_etcd_io.etcd.server.v3.auth.AuthInfo,
          structFieldRef authApplierV3 go!"authInfo" p ↦ i)) [HA Hinfo] as %ar Hpost
    · iframe Hw
      isplitl [HA Hinfo]
      · iframe HA Hinfo
      imodintro
      iintro %Φ'' ⟨Hres, HA, Hi⟩ HΦ''
      ihave Hres := apply.chainResAny_of _ _ _ $$ Hres
      ihave Hres := apply.chainRes_auth_in c p (.ok bi) (apply.principalOf rq) $$ Happ Hi Hres
      iapply Haf $$ [Hres HA]
      · iframe
      inext
      iintro %ar ⟨Hres, HB⟩
      iapply HΦ''
      ihave ⟨%i, Hi, Hres⟩ := apply.chainResAny_auth_out c p (.ok bi) $$ Happ Hres
      dsimp only
      iframe Hres HB
      iexists i; iexact Hi
    ihave ⟨Hi, Hpost⟩ : iprop((∃ i : go_etcd_io.etcd.server.v3.auth.AuthInfo,
        structFieldRef authApplierV3 go!"authInfo" p ↦ i) ∗
        (B ar ∨ (⌜apply.needAdminPermission rq = true⌝ ∗ A ∗ apply.rejectResultIs ar))) $$ [Hpost]
    · icases Hpost with (⟨⟨HB, Hi⟩, -⟩ | ⟨%h, ⟨HA, Hi⟩, Hrej⟩)
      · iframe Hi; ileft; iexact HB
      · isplitl [Hi]
        · iexists _; iexact Hi
        iright; iframe; ipureintro; exact h
    icases Hi with ⟨%info2, Hinfo⟩
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hinfo Hard]
    · inext
      iframe Hard
      iunfold apply.authInfoIdle
      iExactEq Hinfo
      first | rfl | (congr 1; cases info2; rfl) | (congr 1; cases info2; simp [zeroValDef])
    iapply HΦ
    icases Hpost with (HB | ⟨%h, HA, Hrej⟩)
    · ileft
      iframe HB
      iunfold apply.adminPass
      iintro %h
      rw [hna] at h
      cases h.2
    · iright; iframe; ipureintro; first | rfl | (rw [hna] at h; exact h)
  wp_auto
  wp_apply HAdmin $$ [$Hinfo $Hard] as %err ⟨Hinfo, Hard, #HeI, -, #Hadm⟩
  cases err with
  | nil =>
    wp_auto
    wp_apply HApplyI $$ %r %rq %skip %v3 %af
        %(iprop(A ∗ structFieldRef authApplierV3 go!"authInfo" p ↦ apply.principalOf rq))
        %(fun ar => iprop(B ar ∗ ∃ i : go_etcd_io.etcd.server.v3.auth.AuthInfo,
          structFieldRef authApplierV3 go!"authInfo" p ↦ i)) [HA Hinfo] as %ar Hpost
    · iframe Hw
      isplitl [HA Hinfo]
      · iframe HA Hinfo
      imodintro
      iintro %Φ'' ⟨Hres, HA, Hi⟩ HΦ''
      ihave Hres := apply.chainResAny_of _ _ _ $$ Hres
      ihave Hres := apply.chainRes_auth_in c p (.ok bi) (apply.principalOf rq) $$ Happ Hi Hres
      iapply Haf $$ [Hres HA]
      · iframe
      inext
      iintro %ar ⟨Hres, HB⟩
      iapply HΦ''
      ihave ⟨%i, Hi, Hres⟩ := apply.chainResAny_auth_out c p (.ok bi) $$ Happ Hres
      dsimp only
      iframe Hres HB
      iexists i; iexact Hi
    ihave ⟨Hi, Hpost⟩ : iprop((∃ i : go_etcd_io.etcd.server.v3.auth.AuthInfo,
        structFieldRef authApplierV3 go!"authInfo" p ↦ i) ∗
        (B ar ∨ (⌜apply.needAdminPermission rq = true⌝ ∗ A ∗ apply.rejectResultIs ar))) $$ [Hpost]
    · icases Hpost with (⟨⟨HB, Hi⟩, -⟩ | ⟨%h, ⟨HA, Hi⟩, Hrej⟩)
      · iframe Hi; ileft; iexact HB
      · isplitl [Hi]
        · iexists _; iexact Hi
        iright; iframe; ipureintro; exact h
    icases Hi with ⟨%info2, Hinfo⟩
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hinfo Hard]
    · inext
      iframe Hard
      iunfold apply.authInfoIdle
      iExactEq Hinfo
      first | rfl | (congr 1; cases info2; rfl) | (congr 1; cases info2; simp [zeroValDef])
    iapply HΦ
    icases Hpost with (HB | ⟨%h, HA, Hrej⟩)
    · ileft
      iframe HB
      iunfold apply.adminPass
      iintro %_
      iexact Hadm
    · iright; iframe; ipureintro; first | rfl | (rw [hna] at h; exact h)
  | ok e =>
    wp_auto
    wp_alloc ar as Har
    ihave ⟨Har, %Harn⟩ := typedPointsto_not_null_dup _ _ _ $$ Har
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hinfo Hard]
    · inext
      iframe Hard
      iunfold apply.authInfoIdle
      iExactEq Hinfo
      first | rfl | (congr 1; simp [zeroValDef])
    iapply HΦ
    iright
    iframe HA
    isplitr
    · ipureintro; rfl
    iunfold apply.rejectResultIs
    isplitr
    · ipureintro; exact Harn
    iexists _
    iframe Har
    isplitr
    · ipureintro; simp
    iexact HeI

end proof

end EtcdGrove
end Perennial
