/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__UserAdd.lean`. Lean-first (no Rocq
counterpart; the auth plan's E2x, 2026-10-26).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__UserAdd
public import Spec.golang_org.x.crypto.bcrypt.GenerateFromPassword

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.UserAdd.wp_proof
    (h_gen : bcrypt.GenerateFromPassword.spec (GF := GF) (hG := hG)) :
    EtcdServer.UserAdd.spec (GF := GF) (hG := hG) := by
  intro s ctx ast r name pw hpw o b P Q
  wp_start as ⟨#Hast, #Hcost, %Hrnn, #HN, Hpw, Hhpw, #Ho, #Hopts, HP, #Hraft⟩
  wp_auto
  ihave #Hb64 : isPkgInit (PROP := IProp GF) pkg_id.encoding.base64 $$ []
  · solve_pkg_init
  ihave ⟨%e, #He, #Henc⟩ := encoding.base64.base64Init_access $$ Hb64
  iunfold bcryptCostOk at Hcost
  ihave #Hopts' := Hopts
  iunfold auth.userOptsAt at Hopts'
  icases Hopts' with (%Hon | ⟨%Honn, %ms, %uf, %sc, #Hom⟩)
  · obtain ⟨rfl, rfl⟩ := Hon
    wp_auto
    wp_apply wp_string_to_bytes pw as %psl ⟨Hpsl, -⟩
    (try wp_auto)
    wp_apply Hcost as %c -
    wp_apply h_gen $$ [$Hpsl] as %h %err ⟨Hpsl, Hor⟩
    (try wp_auto)
    rcases err with ei | _
    · wp_auto
      iapply HΦ; ileft; iframe HP; ipureintro; exact ⟨rfl, by simp⟩
    icases Hor with (%Herr | ⟨%hs, Hh⟩)
    · exact absurd rfl Herr
    wp_auto
    wp_apply Henc $$ [$Hh] as Hh
    (try wp_auto)
    ipersist Hpw
    ipersist Hhpw
    ihave #Hua : apply.authUserAddIs r ⟨name, [], encoding.base64.stdEnc hs, false⟩ $$ []
    · iunfold apply.authUserAddIs
      iframe #
      ipureintro; exact Hrnn
    ihave #Hr1 := Hraft $$ %(⟨name, [], encoding.base64.stdEnc hs, false⟩ : apply.UserAddModel)
    ispecialize Hr1 $$ []
    · ipureintro
      refine ⟨rfl, rfl, Or.inr ⟨rfl, hs, rfl⟩⟩
    ihave ⟨Hirr, %Hirrn⟩ := typedPointsto_not_null_dup _ _ _ $$ «$a1»
    iStructNamed Hirr
    ipersist ID
    ipersist Range
    ipersist Put
    ipersist DeleteRange
    ipersist Txn
    ipersist Compaction
    ipersist LeaseGrant
    ipersist LeaseRevoke
    ipersist Alarm
    ipersist LeaseCheckpoint
    ipersist AuthEnable
    ipersist AuthDisable
    ipersist AuthStatus
    ipersist Authenticate
    ipersist AuthUserAdd
    ipersist AuthUserDelete
    ipersist AuthUserGet
    ipersist AuthUserChangePassword
    ipersist AuthUserGrantRole
    ipersist AuthUserRevokeRole
    ipersist AuthUserList
    ipersist AuthRoleList
    ipersist AuthRoleAdd
    ipersist AuthRoleDelete
    ipersist AuthRoleGet
    ipersist AuthRoleGrantPermission
    ipersist AuthRoleRevokePermission
    ipersist ClusterVersionSet
    ipersist ClusterMemberAttrSet
    ipersist DowngradeInfoSet
    ipersist DowngradeVersionTest
    ihave #HirrNo : irrNoHdrIs «$a1_ptr» (irrUserAdd _) $$ []
    · iunfold irrNoHdrIs
      simp only [irrUserAdd, apply.irrEmpty, apply.optReqIs, apply.presentIs, apply.irrField]
      isplitr
      · ipureintro; exact Hirrn
      isplitr
      · have h0 : (W64 0 : w64) = 0 := by decide
        rw [h0]; iexact ID
      repeat (isplitr; · iexists _; iframe #; try (ipureintro; simp))
      iexists _; iframe #; try (ipureintro; simp)
    iunfold authRaftOk at Hr1
    ispecialize Hr1 $$ %«$a1_ptr»
    wp_apply Hr1 $$ [$HP $Header] as %resp %err ⟨#Herr, Hout⟩
    · iframe #
    icases Hout with (⟨%He, %l, %Hl, HQ⟩ | ⟨⟨%Hres, %He⟩, HQ⟩)
    · subst He
      subst Hl
      (try wp_auto)
      iapply HΦ
      iright
      iframe Herr
      iunfold authEntryOut
      ileft
      iframe HQ
      ipureintro; rfl
    · subst Hres
      rcases err with ei | _
      · (try wp_auto)
        iapply HΦ
        iright
        iframe Herr
        iunfold authEntryOut
        iright
        iframe HQ
        ipureintro; exact ⟨rfl, He⟩
      · exact absurd rfl He
  · ihave Homf := typedPointsto_split _ _ _ $$ Hom
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Homf
    simp only [Honn, decide_false]
    (try wp_auto)
    cases b
    · (try wp_auto)
      wp_apply wp_string_to_bytes pw as %psl ⟨Hpsl, -⟩
      (try wp_auto)
      wp_apply Hcost as %c -
      wp_apply h_gen $$ [$Hpsl] as %h %err ⟨Hpsl, Hor⟩
      (try wp_auto)
      rcases err with ei | _
      · wp_auto
        iapply HΦ; ileft; iframe HP; ipureintro; exact ⟨rfl, by simp⟩
      icases Hor with (%Herr | ⟨%hs, Hh⟩)
      · exact absurd rfl Herr
      wp_auto
      wp_apply Henc $$ [$Hh] as Hh
      (try wp_auto)
      ipersist Hpw
      ipersist Hhpw
      ihave #Hua : apply.authUserAddIs r ⟨name, [], encoding.base64.stdEnc hs, false⟩ $$ []
      · iunfold apply.authUserAddIs
        iframe #
        ipureintro; exact Hrnn
      ihave #Hr1 := Hraft $$ %(⟨name, [], encoding.base64.stdEnc hs, false⟩ : apply.UserAddModel)
      ispecialize Hr1 $$ []
      · ipureintro
        refine ⟨rfl, rfl, Or.inr ⟨rfl, hs, rfl⟩⟩
      ihave ⟨Hirr, %Hirrn⟩ := typedPointsto_not_null_dup _ _ _ $$ «$a1»
      iStructNamed Hirr
      ipersist ID
      ipersist Range
      ipersist Put
      ipersist DeleteRange
      ipersist Txn
      ipersist Compaction
      ipersist LeaseGrant
      ipersist LeaseRevoke
      ipersist Alarm
      ipersist LeaseCheckpoint
      ipersist AuthEnable
      ipersist AuthDisable
      ipersist AuthStatus
      ipersist Authenticate
      ipersist AuthUserAdd
      ipersist AuthUserDelete
      ipersist AuthUserGet
      ipersist AuthUserChangePassword
      ipersist AuthUserGrantRole
      ipersist AuthUserRevokeRole
      ipersist AuthUserList
      ipersist AuthRoleList
      ipersist AuthRoleAdd
      ipersist AuthRoleDelete
      ipersist AuthRoleGet
      ipersist AuthRoleGrantPermission
      ipersist AuthRoleRevokePermission
      ipersist ClusterVersionSet
      ipersist ClusterMemberAttrSet
      ipersist DowngradeInfoSet
      ipersist DowngradeVersionTest
      ihave #HirrNo : irrNoHdrIs «$a1_ptr» (irrUserAdd _) $$ []
      · iunfold irrNoHdrIs
        simp only [irrUserAdd, apply.irrEmpty, apply.optReqIs, apply.presentIs, apply.irrField]
        isplitr
        · ipureintro; exact Hirrn
        isplitr
        · have h0 : (W64 0 : w64) = 0 := by decide
          rw [h0]; iexact ID
        repeat (isplitr; · iexists _; iframe #; try (ipureintro; simp))
        iexists _; iframe #; try (ipureintro; simp)
      iunfold authRaftOk at Hr1
      ispecialize Hr1 $$ %«$a1_ptr»
      wp_apply Hr1 $$ [$HP $Header] as %resp %err ⟨#Herr, Hout⟩
      · iframe #
      icases Hout with (⟨%He, %l, %Hl, HQ⟩ | ⟨⟨%Hres, %He⟩, HQ⟩)
      · subst He
        subst Hl
        (try wp_auto)
        iapply HΦ
        iright
        iframe Herr
        iunfold authEntryOut
        ileft
        iframe HQ
        ipureintro; rfl
      · subst Hres
        rcases err with ei | _
        · (try wp_auto)
          iapply HΦ
          iright
          iframe Herr
          iunfold authEntryOut
          iright
          iframe HQ
          ipureintro; exact ⟨rfl, He⟩
        · exact absurd rfl He
    · (try wp_auto)
      ipersist Hpw
      ipersist Hhpw
      ihave #Hua : apply.authUserAddIs r ⟨name, pw, hpw, true⟩ $$ []
      · iunfold apply.authUserAddIs
        iframe #
        ipureintro; exact Hrnn
      ihave #Hr1 := Hraft $$ %(⟨name, pw, hpw, true⟩ : apply.UserAddModel)
      ispecialize Hr1 $$ []
      · ipureintro
        exact ⟨rfl, rfl, Or.inl rfl⟩
      ihave ⟨Hirr, %Hirrn⟩ := typedPointsto_not_null_dup _ _ _ $$ «$a1»
      iStructNamed Hirr
      ipersist ID
      ipersist Range
      ipersist Put
      ipersist DeleteRange
      ipersist Txn
      ipersist Compaction
      ipersist LeaseGrant
      ipersist LeaseRevoke
      ipersist Alarm
      ipersist LeaseCheckpoint
      ipersist AuthEnable
      ipersist AuthDisable
      ipersist AuthStatus
      ipersist Authenticate
      ipersist AuthUserAdd
      ipersist AuthUserDelete
      ipersist AuthUserGet
      ipersist AuthUserChangePassword
      ipersist AuthUserGrantRole
      ipersist AuthUserRevokeRole
      ipersist AuthUserList
      ipersist AuthRoleList
      ipersist AuthRoleAdd
      ipersist AuthRoleDelete
      ipersist AuthRoleGet
      ipersist AuthRoleGrantPermission
      ipersist AuthRoleRevokePermission
      ipersist ClusterVersionSet
      ipersist ClusterMemberAttrSet
      ipersist DowngradeInfoSet
      ipersist DowngradeVersionTest
      ihave #HirrNo : irrNoHdrIs «$a1_ptr» (irrUserAdd _) $$ []
      · iunfold irrNoHdrIs
        simp only [irrUserAdd, apply.irrEmpty, apply.optReqIs, apply.presentIs, apply.irrField]
        isplitr
        · ipureintro; exact Hirrn
        isplitr
        · have h0 : (W64 0 : w64) = 0 := by decide
          rw [h0]; iexact ID
        repeat (isplitr; · iexists _; iframe #; try (ipureintro; simp))
        iexists _; iframe #; try (ipureintro; simp)
      iunfold authRaftOk at Hr1
      ispecialize Hr1 $$ %«$a1_ptr»
      wp_apply Hr1 $$ [$HP $Header] as %resp %err ⟨#Herr, Hout⟩
      · iframe #
      icases Hout with (⟨%He, %l, %Hl, HQ⟩ | ⟨⟨%Hres, %He⟩, HQ⟩)
      · subst He
        subst Hl
        (try wp_auto)
        iapply HΦ
        iright
        iframe Herr
        iunfold authEntryOut
        ileft
        iframe HQ
        ipureintro; rfl
      · subst Hres
        rcases err with ei | _
        · (try wp_auto)
          iapply HΦ
          iright
          iframe Herr
          iunfold authEntryOut
          iright
          iframe HQ
          ipureintro; exact ⟨rfl, He⟩
        · exact absurd rfl He

end proof

end EtcdGrove
end Perennial
