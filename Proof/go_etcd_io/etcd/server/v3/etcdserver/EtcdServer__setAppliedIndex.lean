/-
Proof of `Spec/EtcdServer__setAppliedIndex.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__setAppliedIndex

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.cindex go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.server.v3.storage

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- In either auth mode (E3p): the invariant's body is the mode's (`srvAppliedBodyM`). -/
theorem EtcdServer.setAppliedIndex.wp_proofM (on : Bool) :
    EtcdServer.setAppliedIndex.specM (GF := GF) (hG := hG) on := by
  intro s E γr v v' L
  wp_start as ⟨#Hinv, Hpre, #Hc⟩
  iunfold srvAppliedPre at Hpre
  icases Hpre with ⟨Hown, Hpo, #HLv', %hv⟩
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  wp_apply_core sync.atomic.Uint64.wp_Store (srvAppliedIndexAddr s) v' $$ [] [HΦ Hown Hpo]
  · iexact Hatomic
  ihave #Hinv' := Hinv
  iunfold srvAppliedInvM at Hinv'
  iinv Hinv' with Hi Hclose
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  inext
  iunfold srvAppliedBodyM at Hi
  icases Hi with ⟨%vat, %v0, %L0, %M, %p, Hv, Hauth, HM, Hp, %HMk, #HL0, #Hc0, #Hkl⟩
  iexists vat
  iframe Hv
  iintro Hv
  imod Hmask with -
  ihave %Hag := monoNatAuthOwn_agree γr.applied _ _ _ _ $$ Hown Hauth
  have hv0 : v0 = v := by
    have h2 := Hag.2
    unfold uint.nat at h2
    exact (BitVec.eq_of_toNat_eq h2).symm
  subst hv0
  ihave %Hpg := ghostVar_agree γr.pend _ _ _ _ $$ Hpo Hp
  subst Hpg
  imod monoNat_halves_update γr.applied (uint.nat v0) (uint.nat v') (by word) $$ Hown Hauth
    with ⟨Hown, Hauth, #Hlb⟩
  imod ghostVar_update_halves false γr.pend true true $$ Hpo Hp with ⟨Hpo, Hp⟩
  imod Hclose $$ [Hv Hauth HM Hp] with -
  · inext
    iunfold srvAppliedBodyM
    iexists v', v', L, M, false
    iframe Hv Hauth HM Hp Hc HLv' Hkl
    ipureintro
    refine ⟨Int.le_refl _, ?_, HMk.2.2⟩
    intro k L' hk
    left
    rcases HMk.2.1 k L' hk with h | ⟨-, h⟩ <;> omega
  imodintro
  wp_auto
  iapply HΦ
  iunfold srvAppliedOwn
  iframe Hown Hpo
  iunfold appliedAtLeast
  iframe Hlb HLv'

theorem EtcdServer.setAppliedIndex.wp_proof :
    EtcdServer.setAppliedIndex.spec (GF := GF) (hG := hG) :=
  EtcdServer.setAppliedIndex.wp_proofM false

end proof

end EtcdGrove
end Perennial
