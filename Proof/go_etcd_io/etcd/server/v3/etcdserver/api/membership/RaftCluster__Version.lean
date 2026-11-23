/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/membership/RaftCluster__Version.lean`.
Lean-first (no Rocq counterpart); prove-ps2-bootstage1, 2026-11-23 (#34 stage 1): under the
cluster's mutex, the version slot (`rcVerSlot`): nil at `0`, or a read-only version at `1`, whose
rendering `MustParse` reads back.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__Version
public import Spec.github_com.Masterminds.semver.v3.MustParse
public import Spec.github_com.Masterminds.semver.v3.Version__String

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem membership.RaftCluster.Version.wp_proof
    (hMP : semver.MustParse.spec (GF := GF) (hG := hG))
    (hVS : semver.Version.String.spec (GF := GF) (hG := hG)) :
    membership.RaftCluster.Version.spec (GF := GF) (hG := hG) := by
  intro c γcv known
  wp_start as ⟨#Hrc, Hk⟩
  iunfold membership.isRaftClusterV at Hrc
  wp_auto
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hpsem : isPkgInit (PROP := IProp GF) pkg_id.github_com.Masterminds.semver.v3 $$ []
  · iPkgInit
  wp_method_call
  wp_call
  wp_apply sync.Mutex.wp_Lock $$ [$Hrc] as ⟨Hlocked, Hinv⟩
  iunfold membership.rcLockInv at Hinv
  icases Hinv with ⟨%mm, %mem, Hmem, %Hsz, #Hloc, %rp, Hrf, Hrm, Hslot⟩
  iunfold membership.rcVerSlot at Hslot
  icases Hslot with ⟨%vp, %n, Hvp, Ha, Hcase⟩
  wp_auto
  wp_if_destruct
  · -- nil: the version is not known
    icases Hcase with (%Hn | ⟨%Hn1, %x, #Hx, %Hxv⟩)
    rotate_left
    · iexfalso
      ihave %Hnn := typedPointsto_not_null _ x DFrac.discard $$ Hx
      exact absurd rfl Hnn
    ihave %Hk0 : ⌜known = false⌝ $$ [Hk Ha]
    · cases known with
      | false => ipureintro; rfl
      | true =>
        simp only [↓reduceIte]
        ihave %Hle := monoNatLbOwn_valid γcv 1 n 1 $$ Ha Hk
        obtain ⟨_, rfl⟩ := Hn
        omega
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hrc $Hlocked Hmem Hrf Hrm Hvp Ha]
    · inext
      iunfold membership.rcLockInv
      iexists mm, mem
      iframe Hmem Hloc
      isplitr
      · ipureintro; exact Hsz
      iexists rp
      iframe Hrf Hrm
      iunfold membership.rcVerSlot
      iexists null, n
      iframe Hvp Ha
      ileft; ipureintro; exact ⟨rfl, Hn.2⟩
    (try wp_auto)
    iapply HΦ
    ileft; ipureintro; exact ⟨rfl, Hk0⟩
  · icases Hcase with (%Hn | ⟨%Hn1, %x, #Hx, %Hxv⟩)
    · exact absurd Hn.1 Hif
    wp_apply hVS vp DFrac.discard x $$ [] as -
    · iframe #
    wp_apply hMP as %r Hr
    icases Hr with (⟨-, %v, %y, %Hv, #Hy, -⟩ | %Hbad)
    rotate_left
    · exact absurd Hxv Hbad.1
    obtain ⟨rfl, Hvnn⟩ := Hv
    wp_auto
    ihave #Hlb := monoNatLbOwn_get γcv 1 n $$ Ha
    wp_method_call
    wp_call
    wp_apply sync.Mutex.wp_Unlock $$ [$Hrc $Hlocked Hmem Hrf Hrm Hvp Ha]
    · inext
      iunfold membership.rcLockInv
      iexists mm, mem
      iframe Hmem Hloc
      isplitr
      · ipureintro; exact Hsz
      iexists rp
      iframe Hrf Hrm
      iunfold membership.rcVerSlot
      iexists vp, n
      iframe Hvp Ha
      iright
      isplitr
      · ipureintro; exact Hn1
      iexists x
      iframe Hx
      ipureintro; exact Hxv
    (try wp_auto)
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact Hvnn
    isplitr
    · iexists y; iexact Hy
    subst Hn1
    iexact Hlb

end proof

end EtcdGrove
end Perennial
