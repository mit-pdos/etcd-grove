/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/Transport__SendSnapshot.lean`:
`(*rafthttp.Transport).SendSnapshot(m)` (rafthttp stage 7d, D42; an axiom from stage 6d). Lean-first.
Under the write lock, the peer of the message's `To`: its `sendSnap`, or `CloseWithError` if there
is none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport__SendSnapshot
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.peer__sendSnap
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message__fields
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message__CloseWithError
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetTo
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.TransportState

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

/-- `v := m[k]` of a map keyed by member ids that may be `nil` (`mapOrNil`). -/
theorem wp_lookup1_mapOrNil {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (elem_type : go.GoType) [IntoValTyped (GF := GF) V elem_type] (m : Loc) (q : Qp)
    (M : GMap w64 V) (k : w64) :
    {{ mapOrNil (GF := GF) m q M }}
      (App (App (Val (map.lookup1 go_etcd_io.etcd.client.pkg.v3.types.ID.ty elem_type)) (Val #m))
        (Val #k))
    {{ RET #((M !! k).getD (zero_val V)); mapOrNil m q M }} := by
  iintro %Φ Hm HΦ
  iunfold mapOrNil at Hm
  icases Hm with (⟨%Hnil, %HM⟩ | Hm)
  · subst Hnil HM
    rw [show (null : Loc) = map.nil from rfl]
    wp_pures
    simp only [GMap.lookup_empty, Option.getD_none]
    iapply HΦ
    iunfold mapOrNil; ileft; ipureintro; exact ⟨rfl, rfl⟩
  · wp_apply wp_map_lookup1 $$ [$Hm] as Hm
    iapply HΦ
    iunfold mapOrNil; iright; iexact Hm

set_option hygiene false in
/-- The deferred `t.mu.Unlock()`, the lock's state as it was; the return. -/
local macro "unlock_ret" : tactic => `(tactic| (
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Unlock_guard $$ [Hwl Hp Hr Hpm Hrm Hg Hgr]
  · iframe #; iframe Hwl
    inext
    iunfold trLockP; iexists pm, rm, PM, RM, rs', sb; iframe; iframe #
    ipureintro; exact Hrs
  (try wp_auto)
  iapply HΦ; itrivial))

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem rafthttp.Transport.SendSnapshot.wp_proof
    (hSendSnap : rafthttp.peer.sendSnap.spec (GF := GF) (hG := hG))
    (hClose : snap.Message.CloseWithError.spec (GF := GF) (hG := hG))
    (hFields : snap.Message.fields.spec (GF := GF) (hG := hG))
    (hGetTo : raftpb.Message.GetTo.spec (GF := GF) (hG := hG)) :
    rafthttp.Transport.SendSnapshot.spec (GF := GF) (hG := hG) := by
  intro γn t c rs m ml rc
  wp_start as ⟨#Hf, #Hmsg, Hb⟩
  iunfold trFrozen at Hf
  icases Hf with ⟨#Hst, #Hfr⟩
  iunfold trState at Hst
  icases Hst with ⟨#Hfix, #Hprb, #Hstp, #Hgd, %sst, %Rm, #Hssf, #Hss, #Hdir⟩
  ihave ⟨#HfM, -, %rd, %ri, -, -, -, -⟩ := hFields m ml rc $$ Hmsg
  ihave Hri : (go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.rafthttpInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hri with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, ⟨%enf, #Henf⟩⟩
  iunfold netSnapBundle at Hb
  icases Hb with ⟨%st, %sn, %D, #Hml, #HP, HO, %Hst', Hrs, #Himg⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [] as ⟨Hwl, HPl⟩
  · iframe #
  iunfold trLockP at HPl
  icases HPl with ⟨%pm, %rm, %PM, %RM, %rs', %sb, Hp, Hr, Hpm, Hrm, Hg, Hgr, %Hrs, #Hpo, #Hro⟩
  (try wp_auto)
  -- `m.GetTo()`: the raft message's (promoted from the embedded `*raftpb.Message`)
  rw [go_etcd_io.etcd.server.v3.etcdserver.api.snap.Message.TypeAssumptions.ptr_GetTo_unfold.method_unfold]
  (try wp_auto)
  wp_apply hGetTo.1 ml DFrac.discard DFrac.discard false st $$ [$Hml] as -
  (try wp_auto)
  wp_apply wp_lookup1_mapOrNil _ pm _ PM st.msg.To' $$ [Hpm] as Hpm
  · iframe Hpm
  (try wp_auto)
  cases hp : PM !! st.msg.To' with
  | some pi =>
    -- the peer of `To`: its `sendSnap`
    ihave #Hpo' := Hpo
    iunfold peersOk at Hpo'
    ihave Hpi := BigSepM.bigSepM_lookup (Φ := fun id pi => iprop(∃ p : Loc,
      ⌜pi = interface.mkOk (go.GoType.PointerType rafthttp.peer.ty) #p⌝ ∗
      peerOk (netRh γn) c.lid id c.γd c.R p)) hp $$ Hpo'
    icases Hpi with ⟨%pp, %Hpp, #Hpok⟩
    subst Hpp
    simp only [Option.getD_some]
    (try wp_auto)
    wp_apply hSendSnap (netRh γn) c.lid st.msg.To' c.γd c.R pp m ml rc $$ [HO Hrs]
    · iframe #
      rw [show (netRh γn).γn = γn from rfl]
      iunfold snapBundleTo
      iexists st, sn, D
      iframe; iframe #
      ipureintro; exact ⟨Hst'.1, Hst'.2.1, Hst'.2.2, rfl⟩
    unlock_ret
  | none =>
    -- no peer: the message closed with `errMemberNotFound`
    simp only [Option.getD_none]
    (try wp_auto)
    wp_apply hClose m ml rc enf $$ []
    · iframe #
    unlock_ret

end proof

end EtcdGrove
end Perennial
