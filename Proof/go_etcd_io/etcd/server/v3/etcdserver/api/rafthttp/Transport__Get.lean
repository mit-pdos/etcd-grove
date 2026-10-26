/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/Transport__Get.lean`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__Get

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.Transport.Get.wp_proof :
    rafthttp.Transport.Get.spec (GF := GF) (hG := hG) := by
  intro Rh t lid γd R γs γr pid
  wp_start as Htok
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  iunfold trReadTok at Htok
  wp_apply sync.RWMutex.wp_RLock $$ [$Htok] as ⟨Hrl, HP⟩
  iunfold trLockP at HP
  icases HP with ⟨%pm, %rm, %PM, %RM, %rs, %sb, Hp, Hr, Hpm, Hrm, Hg, Hgr, %Hrs, #Hpo, #Hro, Hts⟩
  (try wp_auto)
  -- the entry's facts: `nil`, or a started peer
  ihave #Hent : iprop(⌜(PM !! pid).getD (zero_val GoInterface) = GoInterface.nil⌝ ∨
      ∃ p : Loc, ⌜(PM !! pid).getD (zero_val GoInterface) =
        interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p⌝ ∗ peerOk Rh lid pid γd R p) $$ []
  · cases hk : PM !! pid with
    | none => ileft; ipureintro; rfl
    | some pi =>
      iright
      iunfold peersOk at Hpo
      ihave Hpi := BigSepM.bigSepM_lookup (Φ := fun id pi => iprop(∃ p : Loc,
        ⌜pi = interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p⌝ ∗
        peerOk Rh lid id γd R p)) hk $$ Hpo
      icases Hpi with ⟨%p, %Hp, #Hok⟩
      iexists p
      iframe #
      ipureintro; simp [Hp]
  iunfold mapOrNil at Hpm
  icases Hpm with (⟨%Hpm, %HPM⟩ | Hpm)
  · subst Hpm HPM
    rw [show (null : Loc) = map.nil from rfl]
    (try wp_auto)
    wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hp Hr Hrm Hg Hgr Hts] as Htok
    · iunfold trLockP; iexists map.nil, rm, ∅, RM, rs, sb; iframe; iframe #
      inext
      isplitl
      · iunfold mapOrNil; ileft; ipureintro; exact ⟨rfl, rfl⟩
      ipureintro; exact Hrs
    (try wp_auto)
    iapply HΦ
    iunfold trReadTok
    iframe
    ileft; ipureintro; rfl
  · wp_apply wp_map_lookup1 $$ [$Hpm] as Hpm
    (try wp_auto)
    wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hp Hr Hpm Hrm Hg Hgr Hts] as Htok
    · iunfold trLockP; iexists pm, rm, PM, RM, rs, sb; iframe; iframe #
      inext
      isplitl
      · iunfold mapOrNil; iright; iframe
      ipureintro; exact Hrs
    (try wp_auto)
    iapply HΦ
    iunfold trReadTok
    iframe
    iexact Hent

end proof

end EtcdGrove
end Perennial
