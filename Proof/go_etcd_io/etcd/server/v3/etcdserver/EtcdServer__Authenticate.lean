/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__Authenticate.lean` (C1's A4,
2026-10-31). Lean-first (no Rocq counterpart).

The read index (`isReadNotify`, from the server's read view, at the committed index `0` and no
deposit); then the retry loop, its invariant the run's slots, the password field and the last
round's answer: each round `CheckPassword` and `GenTokenPrefix` (`authnStoreOk`), one proposal
(`authnRaft_on`, its id from `□ |==> idCred`) and `Revision`; the `defer` clears the password.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Authenticate
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthnOn
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__AuthStore
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Error
public import Spec.errors.Is

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

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

set_option maxHeartbeats 4000000 in
theorem EtcdServer.Authenticate.wp_proof
    (hRR : EtcdServer.raftRequest.specM (GF := GF) (hG := hG) true)
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hAS : EtcdServer.AuthStore.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hStr : zap.String.spec (GF := GF) (hG := hG))
    (hZE : zap.Error.spec (GF := GF) (hG := hG))
    (hIs : errors.Is.spec (GF := GF) (hG := hG)) :
    EtcdServer.Authenticate.spec (GF := GF) (hG := hG) := by
  intro s E ρ γr γa ctx cd ast r name pw F hγa
  wp_start as ⟨#Hsrv, #Hrdv, #Hast, #Hauthn, #HNR, #HF, #Hctx, %Hrn, #HN, Hpw, Hlt, Hlg, Hrr, Hrd⟩
  ihave #Hrd' := Hrdv
  iunfold isServerReadM at Hrd'
  icases Hrd' with ⟨%w, #Hw⟩
  iunfold srvReadFieldsAtM at Hw
  icases Hw with ⟨#Hread, #HisRead, -, -, -, -, -, -, -, -, #Hlgf, %Hlgn, -⟩
  ihave #Hauthn' := Hauthn
  iunfold authnStoreOk at Hauthn'
  icases Hauthn' with ⟨%ai, %Hai, #HCP, #HGT, #HRev⟩
  cases Hai
  ihave #HisRead' := HisRead
  iunfold isReadNotify at HisRead'
  iunfold srvReadReader at Hrr
  icases Hrr with ⟨%rd, #Hrd0, Hrr⟩
  icombine Hread Hrd0 gives %Hrdeq
  subst Hrdeq
  imod (monoNatLbOwn_0 (GF := GF) γr.committed) with #H0
  ihave #Hc0 : committedAtLeast γr (W64 0) $$ []
  · unfold committedAtLeast
    rw [show uint.nat (W64 0) = 0 from rfl]
    iexact H0
  imod saved_pred_alloc (fun (_ : List EntryModel) => iprop(True)) DFrac.discard trivial with ⟨%g, #Hg⟩
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  ihave #Hdep : kvDep (GF := GF) γr.kv (fun (_ : List EntryModel) => iprop(True)) (kvStM true γr.kv) $$ []
  · iunfold kvDep; iright; ipureintro; rfl
  wp_apply HisRead' $$ %ctx %cd %(W64 0) %g %(fun (_ : List EntryModel) => iprop(True)) [Hrr]
    as %rerr ⟨Hrr, #HrE, -⟩
  · iframe Hdep Hg Hc0; iframe Hrr; iunfold mvcc.txnCtx; iright; iexact Hctx
  ihave Hrr : srvReadReader s γr $$ [Hrr]
  · iunfold srvReadReader; iexists _; iframe Hread Hrr
  (try wp_auto)
  cases rerr with
  | ok rei =>
    wp_auto
    iapply HΦ
    iframe Hlt Hlg Hrr Hrd HrE
    isplitl [Hpw]
    · iexists pw; iframe Hpw; ipureintro; intro h; cases h
    iright; ipureintro; exact ⟨rfl, nofun⟩
  | nil =>
    (try wp_auto)
    wp_apply hLg s w.lg $$ [Hlg] as ⟨-, Hlg⟩
    · iframe #; iframe Hlg; ipureintro; exact Hlgn
    (try wp_auto)
    ihave #Papkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth $$ []
    · iPkgInit
    ihave #Perr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
    · iPkgInit
    ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
    · iPkgInit
    ihave #HnE := apply.authErrVar_of_pkg auth.AuthErr.authNotEnabled $$ Papkg
    simp only [auth.AuthErr.var] at *
    iunfold go_etcd_io.etcd.server.v3.auth.authErrVar at HnE
    icases HnE with ⟨%eN, #HeN, %HlN, -⟩
    ihave HI : (∃ m : GoInterface, resp_ptr ↦ m) $$ [resp]
    · iexists _; iexact resp
    wp_for HI
    wp_apply hAS s (GoInterface.ok ast) $$ []
    · iframe #
    (try wp_auto)
    wp_apply HCP $$ %name %pw [Hrd] as %rev %cerr ⟨Hrd, #HcE⟩
    · iexact Hrd
    (try wp_auto)
    cases cerr with
    | ok cei =>
      wp_auto
      ihave #HT := applyErrIs_tree _ $$ HcE
      ihave ⟨%S, %M, #Htree, %HS⟩ := HT $$ %(GoInterface.ok eN)
      have hpt : ptrTarget (GoInterface.ok eN) := fun tii h => by cases h; exact HlN.1
      wp_apply hIs S M _ (GoInterface.ok eN) hpt (HS.2 hpt) $$ [] as %b -
      · iframe #; ipureintro; exact HS.1
      cases b
      · wp_auto
        wp_apply hStr as %f1 -
        (try wp_auto)
        wp_apply hZE as %f2 -
        (try wp_auto)
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %fsl ⟨-, -⟩
        (try wp_auto)
        wp_apply hWarn w.lg $$ []
        · iframe #; ipureintro; exact Hlgn
        (try wp_auto)
        wp_for_post
        rw [decide_eq_false Hrn]
        wp_auto
        iapply HΦ
        iframe Hlt Hlg Hrr Hrd HcE
        isplitl [Hpw]
        · iexists _; iframe Hpw; ipureintro; intro h; cases h
        iright; ipureintro; exact ⟨rfl, nofun⟩
      · wp_auto
        wp_for_post
        rw [decide_eq_false Hrn]
        wp_auto
        iapply HΦ
        iframe Hlt Hlg Hrr Hrd HcE
        isplitl [Hpw]
        · iexists _; iframe Hpw; ipureintro; intro h; cases h
        iright; ipureintro; exact ⟨rfl, nofun⟩
    | nil =>
      wp_auto
      wp_apply hAS s (GoInterface.ok ast) $$ []
      · iframe #
      (try wp_auto)
      wp_apply HGT as %pre %terr %Hterr
      obtain ⟨rfl, Hpre⟩ := Hterr
      wp_auto
      ihave ⟨Hr0, %Hr0n⟩ := typedPointsto_not_null_dup _ _ _ $$ «$r0»
      iStructNamed Hr0
      ipersist Name
      ipersist Password
      ipersist SimpleToken
      iclear state unknownFields sizeCache
      ihave #Hau : apply.authenticateIs «$r0_ptr» ⟨name, [], pre⟩ $$ []
      · iunfold apply.authenticateIs
        iframe #
        ipureintro; exact Hr0n
      iclear Name Password SimpleToken
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
      ihave #HirrNo : irrNoHdrIs «$a1_ptr» (irrAuthenticate ⟨name, [], pre⟩) $$ []
      · iunfold irrNoHdrIs
        simp only [irrAuthenticate, apply.irrEmpty, apply.optReqIs, apply.presentIs, apply.irrField]
        isplitr
        · ipureintro; exact Hirrn
        isplitr
        · have h0 : (W64 0 : w64) = 0 := by decide
          rw [h0]; iexact ID
        repeat (isplitr; · iexists _; iframe #; try (ipureintro; simp))
        iexists _; iframe #; try (ipureintro; simp)
      ihave Hid := HNR
      imod Hid
      wp_apply authnRaft_on hRR s E ρ γa hγa ctx cd «$a1_ptr» name pre Hpre F $$ [Hlt Hrd Hid Header]
        as %resp %rerr ⟨Hlt, Hrd, #HrE, Hout⟩
      · iframe #; iframe Hlt Hrd Hid
        iexists _; iexact Header
      (try wp_auto)
      icases Hout with (⟨%He, %rp, %v, %Hresp, Hrp, #Ht⟩ | ⟨%Hre, %Hne⟩)
      · subst He
        wp_auto
        wp_apply hAS s (GoInterface.ok ast) $$ []
        · iframe #
        (try wp_auto)
        wp_apply HRev as %x -
        (try wp_auto)
        wp_if_destruct
        · wp_for_post
          subst Hresp
          wp_auto
          rw [decide_eq_false Hrn]
          wp_auto
          iapply HΦ
          iframe Hlt Hlg Hrr Hrd
          isplitl [Hpw]
          · iexists _; iframe Hpw; ipureintro; intro _; rfl
          isplitr
          · iapply applyErrIs_nil
          ileft
          isplitr
          · ipureintro; rfl
          iexists v
          iframe Hrp Ht
        · (try wp_auto)
          wp_apply hInfo w.lg $$ []
          · iframe #; ipureintro; exact Hlgn
          wp_for_post
          iframe
          iexists _; iframe
      · cases rerr with
        | nil => exact absurd rfl Hne
        | ok rei =>
          wp_auto
          wp_for_post
          rw [decide_eq_false Hrn]
          wp_auto
          iapply HΦ
          iframe Hlt Hlg Hrr Hrd HrE
          isplitl [Hpw]
          · iexists _; iframe Hpw; ipureintro; intro h; cases h
          iright; ipureintro; exact ⟨rfl, nofun⟩

end proof

end EtcdGrove
end Perennial
