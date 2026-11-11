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

/-- In either auth mode (E3p): the invariant's body is the mode's (`srvAppliedBodyM`); (R2d-4) a
replay's store below the ghost applied index keeps the invariant (the atomic may lag). -/
theorem EtcdServer.setAppliedIndex.wp_proof :
    EtcdServer.setAppliedIndex.spec (GF := GF) (hG := hG) := by
  intro s E γr v v' L rep
  cases rep
  case true =>
    -- (R2d-4) a replay below the ghost applied index: the atomic store only
    simp only [↓reduceIte]
    wp_start as ⟨#Hinv, Hown, %hle⟩
    ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
    · iPkgInit
    wp_auto
    wp_apply_core sync.atomic.Uint64.wp_Store (srvAppliedIndexAddr s) v' $$ [] [HΦ Hown]
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
    iunfold srvAppliedOwn at Hown
    icases Hown with ⟨Hown, Hpo⟩
    ihave %Hag := monoNatAuthOwn_agree γr.applied _ _ _ _ $$ Hown Hauth
    have hv0 : v0 = v := by
      have h2 := Hag.2
      unfold uint.nat at h2
      exact (BitVec.eq_of_toNat_eq h2).symm
    subst hv0
    imod Hclose $$ [Hv Hauth HM Hp] with -
    · inext
      iunfold srvAppliedBodyM
      iexists v', v0, L0, M, p
      iframe Hv Hauth HM Hp HL0 Hc0 Hkl
      ipureintro
      exact ⟨hle, HMk.2⟩
    imodintro
    wp_auto
    iapply HΦ
    iunfold srvAppliedOwn
    iframe Hown Hpo
  simp only [Bool.false_eq_true, ↓reduceIte]
  wp_start as ⟨#Hinv, Hpre, #Hc, #Hpub⟩
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
  ihave #Hkl' := kvLogsPubM_move E.authOn E γr M v0 v' $$ [Hkl Hpub]
  · iframe Hkl Hpub
  imod Hclose $$ [Hv Hauth HM Hp] with -
  · inext
    iunfold srvAppliedBodyM
    iexists v', v', L, M, false
    iframe Hv Hauth HM Hp Hc HLv' Hkl'
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

end proof

end EtcdGrove
end Perennial
