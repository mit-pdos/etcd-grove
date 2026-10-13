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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.setAppliedIndex.wp_proof :
    EtcdServer.setAppliedIndex.spec (GF := GF) (hG := hG) := by
  intro s E γr v v' L hlt
  wp_start as ⟨#Hinv, Hown, #Hc⟩
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  wp_apply_core sync.atomic.Uint64.wp_Store (srvAppliedIndexAddr s) v' $$ [] [HΦ Hown]
  · iexact Hatomic
  ihave #Hinv' := Hinv
  iunfold srvAppliedInv at Hinv'
  iinv Hinv' with Hi Hclose
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  inext
  icases Hi with ⟨%v0, %L0, %M, Hv, Hauth, HM, %HMk, #HL0, #Hc0⟩
  iexists v0
  iframe Hv
  iintro Hv
  imod Hmask with -
  iunfold srvAppliedOwn at Hown
  ihave %Hag := monoNatAuthOwn_agree γr.applied _ _ _ _ $$ Hown Hauth
  have hv0 : v0 = v := by
    have h2 := Hag.2
    unfold uint.nat at h2
    exact (BitVec.eq_of_toNat_eq h2).symm
  subst hv0
  imod monoNat_halves_update γr.applied (uint.nat v0) (uint.nat v') (by word) $$ Hown Hauth
    with ⟨Hown, Hauth, #Hlb⟩
  have hfresh : M.lookup v' = none := by
    cases h : M.lookup v' with
    | none => rfl
    | some L' => have := HMk v' L' h; omega
  imod ghost_map_insert_persist v' L hfresh $$ HM with ⟨HM, #HLv'⟩
  imod Hclose $$ [Hv Hauth HM] with -
  · inext
    iexists v', L, M.insert v' L
    iframe Hv Hauth HM Hc
    isplitr
    · ipureintro
      intro k L' hk
      by_cases hkv : v' = k
      · subst hkv; exact Int.le_refl _
      · have hk' : M.lookup k = some L' := by
          rw [← GMap.lookup_insert_ne M L hkv]; exact hk
        have := HMk k L' hk'; omega
    · iunfold appliedLogAt; iexact HLv'
  imodintro
  wp_auto
  iapply HΦ
  iunfold srvAppliedOwn
  iframe Hown
  iunfold appliedAtLeast
  iframe Hlb
  iunfold appliedLogAt
  iexact HLv'

end proof

end EtcdGrove
end Perennial
