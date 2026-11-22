/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/Transport__ActiveSince.lean`
(rdslot, 2026-11-22; until then a trust-boundary axiom). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__ActiveSince
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peer__activeSince

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

theorem rafthttp.Transport.ActiveSince.wp_proof
    (hPA : rafthttp.peer.activeSince.spec (GF := GF) (hG := hG)) :
    rafthttp.Transport.ActiveSince.spec (GF := GF) (hG := hG) := by
  intro γn t c id
  wp_start as Htok
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
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
  wp_apply wp_lookup2_mapOrNil _ pm _ PM id $$ [$Hpm] as Hpm
  (try wp_auto)
  cases hp : PM !! id with
  | some pi =>
    ihave #Hpo' := Hpo
    iunfold peersOk at Hpo'
    ihave Hpi := BigSepM.bigSepM_lookup (Φ := fun id pi => iprop(∃ p : Loc,
      ⌜pi = interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p⌝ ∗
      peerOk (netRh γn) c.lid id c.γd c.R p)) hp $$ Hpo'
    icases Hpi with ⟨%pp, %Hpp, #Hpok⟩
    subst Hpp
    simp only [Option.getD_some, Option.isSome_some, _root_.decide_true]
    (try wp_auto)
    wp_apply hPA (netRh γn) c.lid id c.γd c.R pp $$ [] as %tm -
    · iframe #
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
  | none =>
    simp only [Option.getD_none, Option.isSome_none, Bool.false_eq_true, _root_.decide_false]
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
