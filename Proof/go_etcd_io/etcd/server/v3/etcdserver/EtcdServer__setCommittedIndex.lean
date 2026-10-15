/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__setCommittedIndex.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__setCommittedIndex

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.setCommittedIndex.wp_proof :
    EtcdServer.setCommittedIndex.spec (GF := GF) (hG := hG) := by
  intro s γr v v' hle
  wp_start as ⟨#Hinv, Hown⟩
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  wp_apply_core sync.atomic.Uint64.wp_Store (srvCommittedIndexAddr s) v' $$ [] [HΦ Hown]
  · iexact Hatomic
  ihave #Hinv' := Hinv
  iunfold srvCommittedInv at Hinv'
  iinv Hinv' with Hi Hclose
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  inext
  icases Hi with ⟨%v0, Hv, Hauth⟩
  iexists v0
  iframe Hv
  iintro Hv
  imod Hmask with -
  iunfold srvCommittedOwn at Hown
  ihave %Hag := monoNatAuthOwn_agree γr.committed _ _ _ _ $$ Hown Hauth
  have hv0 : v0 = v := by
    have h2 := Hag.2
    unfold uint.nat at h2
    exact (BitVec.eq_of_toNat_eq h2).symm
  subst hv0
  imod monoNat_halves_update γr.committed (uint.nat v0) (uint.nat v') (by word) $$ Hown Hauth
    with ⟨Hown, Hauth, #Hlb⟩
  imod Hclose $$ [Hv Hauth] with -
  · inext; iexists v'; iframe Hv Hauth
  imodintro
  wp_auto
  iapply HΦ
  iunfold srvCommittedOwn
  iframe Hown
  iunfold committedAtLeast
  iexact Hlb

end proof

end EtcdGrove
end Perennial
