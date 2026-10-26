/-
**`Transport.CutPeer` and `MendPeer`, over the transport's lock** (rafthttp stage 6c; their axioms'
statements are restated over these in 6d). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TransportInv
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peer__Pause
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peer__Resume

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
variable [PeerPausable]

set_option hygiene false in
/-- `CutPeer`'s and `MendPeer`'s body: the read-locked lookups (no remote: `id ∉ rs.1`), then the
peer's `M` (`hM`), if any. -/
local macro "cut_body" : tactic => `(tactic| (
  wp_start as ⟨Htok, #Hfr⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  iunfold trReadTok at Htok
  wp_apply sync.RWMutex.wp_RLock $$ [Htok] as ⟨Hrl, HP⟩
  · iframe Htok
  iunfold trLockP at HP
  icases HP with ⟨%pm, %rm, %PM, %RM, %rs', %sb, Hp, Hr, Hpm, Hrm, Hg, Hgr, %Hrs, #Hpo, #Hro, Hts⟩
  imod trRemotes_agree γr rs rs' sb _ $$ Hfr Hgr with ⟨Hgr, %Heq⟩
  subst Heq
  have Hnone : RM !! id = none := by
    cases h : RM !! id with
    | none => rfl
    | some _ => exact absurd (Hrs.1 id (by simp [h])) Hid
  (try wp_auto)
  wp_apply wp_lookup2_mapOrNil _ pm _ PM id $$ [Hpm] as Hpm
  · iframe Hpm
  (try wp_auto)
  wp_apply wp_lookup2_mapOrNil _ rm _ RM id $$ [Hrm] as Hrm
  · iframe Hrm
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RUnlock $$ [Hrl Hp Hr Hpm Hrm Hg Hgr Hts] as Htok
  · iframe Hrl
    iunfold trLockP; iexists pm, rm, PM, RM, rs', sb; iframe; iframe #
    (try inext)
    ipureintro; exact Hrs
  (try wp_auto)
  rw [Hnone]
  simp only [Option.getD_none, Option.isSome_none, Bool.false_eq_true, _root_.decide_false]
  cases hp : PM !! id with
  | some pi =>
    iunfold peersOk at Hpo
    ihave Hpi := BigSepM.bigSepM_lookup (Φ := fun id pi => iprop(∃ p : Loc,
      ⌜pi = interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p⌝ ∗
      peerOk Rh lid id γd R p)) hp $$ Hpo
    icases Hpi with ⟨%pp, %Hpp, #Hpok⟩
    subst Hpp
    simp only [Option.getD_some, Option.isSome_some, _root_.decide_true]
    (try wp_auto)
    rw [ite_cond_eq_true _ _ (eq_true PeerPausable.pausable)]
    (try wp_auto)
    wp_apply hM Rh lid id γd R pp $$ []
    · iframe #
    (try wp_auto)
    iapply HΦ; iunfold trReadTok; iexact Htok
  | none =>
    simp only [Option.getD_none, Option.isSome_none, Bool.false_eq_true, _root_.decide_false]
    (try wp_auto)
    iapply HΦ; iunfold trReadTok; iexact Htok))

/-- **`t.CutPeer(id)`** with a reader's token, `id` no remote (`id ∉ rs.1`, the ids `AddRemote` was
called for, frozen): it returns, the peer of `id`, if any, paused. -/
theorem rafthttp.Transport.CutPeer_core
    (hM : rafthttp.peer.Pause.spec (GF := GF) (hG := hG))
    (Rh : RaftHttp GF) (t : Loc) (lid : w64) (γd : GName) (R : IProp GF) (γs γr : GName)
    (rs : trIds) (id : w64) (Hid : id ∉ rs.1) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trReadTok Rh t lid γd R γs γr ∗ trRemotesFrozen γr rs }}
      (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"CutPeer")) (Val #id))
    {{ RET #(); trReadTok Rh t lid γd R γs γr }} := by
  cut_body

/-- **`t.MendPeer(id)`**, as `CutPeer`: the peer of `id`, if any, resumed. -/
theorem rafthttp.Transport.MendPeer_core
    (hM : rafthttp.peer.Resume.spec (GF := GF) (hG := hG))
    (Rh : RaftHttp GF) (t : Loc) (lid : w64) (γd : GName) (R : IProp GF) (γs γr : GName)
    (rs : trIds) (id : w64) (Hid : id ∉ rs.1) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
        trReadTok Rh t lid γd R γs γr ∗ trRemotesFrozen γr rs }}
      (App (Val (t @!! go.GoType.PointerType rafthttp.Transport.ty @!! go!"MendPeer")) (Val #id))
    {{ RET #(); trReadTok Rh t lid γd R γs γr }} := by
  cut_body

end proof

end EtcdGrove
end Perennial
