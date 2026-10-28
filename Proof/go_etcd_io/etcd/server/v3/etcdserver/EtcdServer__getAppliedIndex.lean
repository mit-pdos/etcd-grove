/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__getAppliedIndex.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__getAppliedIndex

@[expose] public section

set_option linter.unusedSectionVars false

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

/-- In either auth mode (E3r): the invariant's body is the mode's (`srvAppliedBodyM`). -/
theorem EtcdServer.getAppliedIndex.wp_proofM (on : Bool) :
    EtcdServer.getAppliedIndex.specM (GF := GF) (hG := hG) on := by
  intro s E γr
  wp_start as #Hl
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  iunfold srvAppliedInvM at Hl
  wp_auto
  wp_apply_core sync.atomic.Uint64.wp_Load (structFieldRef EtcdServer go!"appliedIndex" s)
    (DFrac.own 1) $$ [] [HΦ «$res0»]
  · iexact Hatomic
  iinv Hl with Hi Hclose
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  inext
  iunfold srvAppliedBodyM at Hi
  icases Hi with ⟨%v0, %a0, %L0, %M, %p, Hv, Hauth, HM, Hp, %HMk, #HL0, #Hc0, #Hkl⟩
  iexists v0
  iframe Hv
  iintro Hv
  imod Hmask with -
  ihave #Hlb := monoNatLbOwn_get γr.applied _ _ $$ Hauth
  -- (D22 J5) the atomic at most the ghost index: a lower bound of it
  ihave #Hlb' := monoNatLbOwn_le (uint.nat v0) (by have := HMk.1; word) $$ Hlb
  imod Hclose $$ [Hv Hauth HM Hp] with -
  · inext; iunfold srvAppliedBodyM; iexists v0, a0, L0, M, p; iframe Hv Hauth HM Hp HL0 Hc0 Hkl
    ipureintro; exact HMk
  imodintro
  wp_auto
  iapply HΦ
  iunfold appliedAtLeast
  iexact Hlb'

theorem EtcdServer.getAppliedIndex.wp_proof : EtcdServer.getAppliedIndex.spec (GF := GF) (hG := hG) :=
  EtcdServer.getAppliedIndex.wp_proofM false

end proof

end EtcdGrove
end Perennial
