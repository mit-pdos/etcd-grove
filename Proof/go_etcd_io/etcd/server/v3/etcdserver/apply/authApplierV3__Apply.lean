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
  wp_auto
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
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, Hinfo⟩
  iunfold apply.authInfoOwn at Hinfo
  icases Hinfo with ⟨%info, Hinfo⟩
  wp_join iprop(∃ info' : go_etcd_io.etcd.server.v3.auth.AuthInfo,
      structFieldRef authApplierV3 go!"authInfo" p ↦ info' ∗ aa_ptr ↦ p ∗ r_ptr ↦ r)
    with [Hinfo aa r] as ⟨%info', Hinfo, aa, r⟩
  · cases hh : rq.header with
    | none =>
      simp only [apply.optReqIs]
      icases Hhdr with %Hnull
      exact absurd Hnull Hif
    | some hm =>
      simp only [apply.optReqIs]
      iunfold apply.headerIs at Hhdr
      icases Hhdr with ⟨%Hhn, -, #HU, #HR⟩
      wp_auto
      isplitr
      · ipureintro; rfl
      iexists _; iframe
  wp_apply (hNA ip rq) $$ [$Hirr] as %b %Hb
  subst Hb
  cases hna : apply.needAdminPermission rq
  · wp_auto
    wp_apply HApplyI $$ %r %rq %skip %v3 %af %(iprop(A ∗ apply.authInfoOwn p))
        %(fun ar => iprop(B ar ∗ apply.authInfoOwn p)) [HA Hinfo] as %ar Hpost
    · iframe Hw
      isplitl [HA Hinfo]
      · iframe HA; iunfold apply.authInfoOwn; iexists _; iexact Hinfo
      imodintro
      iintro %Φ'' ⟨Hres, HA, Hi⟩ HΦ''
      ihave Hres := apply.chainRes_auth_in c p (.ok bi) $$ Happ Hi Hres
      iapply Haf $$ [Hres HA]
      · iframe
      inext
      iintro %ar ⟨Hres, HB⟩
      iapply HΦ''
      ihave ⟨Hi, Hres⟩ := apply.chainRes_auth_out c p (.ok bi) $$ Happ Hres
      dsimp only
      iframe
    ihave ⟨Hi, Hpost⟩ : iprop(apply.authInfoOwn p ∗
        (B ar ∨ (⌜apply.needAdminPermission rq = true⌝ ∗ A ∗ apply.rejectResultIs ar))) $$ [Hpost]
    · icases Hpost with (⟨HB, Hi⟩ | ⟨%h, ⟨HA, Hi⟩, Hrej⟩)
      · iframe Hi; ileft; iexact HB
      · iframe Hi; iright; iframe; ipureintro; exact h
    iunfold apply.authInfoOwn at Hi
    icases Hi with ⟨%info2, Hinfo⟩
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hinfo]
    · inext; iunfold apply.authInfoOwn; iexists _; iexact Hinfo
    iapply HΦ
    icases Hpost with (HB | ⟨%h, HA, Hrej⟩)
    · ileft; iexact HB
    · iright; iframe; ipureintro; first | rfl | (rw [hna] at h; exact h)
  wp_auto
  wp_apply HAdmin $$ [$Hinfo] as %err ⟨Hinfo, #HeI⟩
  cases err with
  | nil =>
    wp_auto
    wp_apply HApplyI $$ %r %rq %skip %v3 %af %(iprop(A ∗ apply.authInfoOwn p))
        %(fun ar => iprop(B ar ∗ apply.authInfoOwn p)) [HA Hinfo] as %ar Hpost
    · iframe Hw
      isplitl [HA Hinfo]
      · iframe HA; iunfold apply.authInfoOwn; iexists _; iexact Hinfo
      imodintro
      iintro %Φ'' ⟨Hres, HA, Hi⟩ HΦ''
      ihave Hres := apply.chainRes_auth_in c p (.ok bi) $$ Happ Hi Hres
      iapply Haf $$ [Hres HA]
      · iframe
      inext
      iintro %ar ⟨Hres, HB⟩
      iapply HΦ''
      ihave ⟨Hi, Hres⟩ := apply.chainRes_auth_out c p (.ok bi) $$ Happ Hres
      dsimp only
      iframe
    ihave ⟨Hi, Hpost⟩ : iprop(apply.authInfoOwn p ∗
        (B ar ∨ (⌜apply.needAdminPermission rq = true⌝ ∗ A ∗ apply.rejectResultIs ar))) $$ [Hpost]
    · icases Hpost with (⟨HB, Hi⟩ | ⟨%h, ⟨HA, Hi⟩, Hrej⟩)
      · iframe Hi; ileft; iexact HB
      · iframe Hi; iright; iframe; ipureintro; exact h
    iunfold apply.authInfoOwn at Hi
    icases Hi with ⟨%info2, Hinfo⟩
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hinfo]
    · inext; iunfold apply.authInfoOwn; iexists _; iexact Hinfo
    iapply HΦ
    icases Hpost with (HB | ⟨%h, HA, Hrej⟩)
    · ileft; iexact HB
    · iright; iframe; ipureintro; first | rfl | (rw [hna] at h; exact h)
  | ok e =>
    wp_auto
    wp_alloc ar as Har
    ihave ⟨Har, %Harn⟩ := typedPointsto_not_null_dup _ _ _ $$ Har
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hinfo]
    · inext; iunfold apply.authInfoOwn; iexists _; iexact Hinfo
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
