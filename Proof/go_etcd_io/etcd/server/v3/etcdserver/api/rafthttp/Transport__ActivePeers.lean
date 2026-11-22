/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/Transport__ActivePeers.lean`
(rdslot, 2026-11-22). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__ActivePeers
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peer__activeSince
public import Perennial.Proof.time.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.Transport.ActivePeers.wp_proof
    (hPA : rafthttp.peer.activeSince.spec (GF := GF) (hG := hG)) :
    rafthttp.Transport.ActivePeers.spec (GF := GF) (hG := hG) := by
  intro γn t c
  wp_start as Htok
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Ptime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  iunfold transportTok at Htok
  iunfold trReadTok at Htok
  wp_apply sync.RWMutex.wp_RLock $$ [$Htok] as ⟨Hrl, HP⟩
  iunfold trLockP at HP
  icases HP with ⟨%pm, %rm, %PM, %RM, %T, %rs, %sb, Hp, Hr, Hpm, Hrm, Hg, Hgr, %Hrs, #Hpo, #Hro,
    Hts⟩
  (try wp_auto)
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_range_mapOrNil _ _ pm _ PM _ (fun id pi => iprop(∃ p : Loc,
      ⌜pi = interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p⌝ ∗
      peerOk (netRh γn) c.lid id c.γd c.R p))
    iprop((∃ x : GoInterface, p_ptr ↦ x) ∗ ∃ n : w64, cnt_ptr ↦ n) $$ Hpm [] [p cnt]
  · iunfold peersOk at Hpo; iexact Hpo
  · iframe
  isplitr
  · imodintro
    iintro %k %pi %Hk ⟨⟨%x, p⟩, %n, cnt⟩ ⟨%pp, %Hpp, #Hpok⟩
    subst Hpp
    (try wp_auto)
    wp_apply hPA (netRh γn) c.lid k c.γd c.R pp $$ [] as %tm -
    · iframe #
    wp_apply _root_.Perennial.time.Time.wp_IsZero
    (try wp_auto)
    wp_if_destruct
    · (try wp_auto)
      isplitr
      · ipureintro; first | rfl | trivial
      iframe
    · (try wp_auto)
      isplitr
      · ipureintro; first | rfl | trivial
      iframe
  iintro Hpm ⟨-, %n, cnt⟩
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl Hp Hr Hpm Hrm Hg Hgr Hts] as Htok
  · iunfold trLockP; iexists pm, rm, PM, RM, T, rs, sb; iframe; iframe #
    (try inext)
    ipureintro; exact Hrs
  (try wp_auto)
  iapply HΦ
  iunfold transportTok
  iunfold trReadTok
  iexact Htok

end proof

end EtcdGrove
end Perennial
