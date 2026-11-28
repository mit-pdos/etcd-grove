/-
Proof of `Spec/EtcdServer__getTxPostLockInsideApplyHook.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__getTxPostLockInsideApplyHook
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__ConsistentApplyingIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__UnsafeConsistentIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__SetConsistentIndex

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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.getTxPostLockInsideApplyHook.wp_proof
    (hA : consistentIndex.ConsistentApplyingIndex.spec (GF := GF) (hG := hG))
    (hU : consistentIndex.UnsafeConsistentIndex.spec (GF := GF) (hG := hG))
    (hS : consistentIndex.SetConsistentIndex.spec (GF := GF) (hG := hG)) :
    EtcdServer.getTxPostLockInsideApplyHook.spec (GF := GF) (hG := hG) := by
  intro s γ ci cl TM
  wp_start as #Hsrv
  wp_alloc_auto
  wp_pures
  wp_alloc sp as Hsp
  ipersist Hsp
  wp_auto
  iapply HΦ
  isplitr
  · ipureintro; simp [func.nil]
  iunfold hookSpec
  iintro %st %i %t %rt %b
  wp_start as ⟨HL, Hst, Happ, Hrt, Hbe, %Hpre, #HP⟩
  obtain ⟨hp, hi, hlt, hce, hld⟩ := Hpre
  ihave #Hcipkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex $$ []
  · iPkgInit
  iunfold isServerCI at Hsrv
  icases Hsrv with ⟨#Hfld, #Hci, #Hinv⟩
  wp_auto
  wp_apply hA ci i t $$ [$Happ] as Happ
  (try wp_auto)
  wp_apply_core (wp_ci_unsafeGet (Rw := TRow.triv) hU (srvCITriple0 cl) γ ci b rt st hp) $$ [Hst Hbe Hrt]
      [HΦ HL Happ applyingIdx applyingTerm]
  · iframe Hcipkg Hci Hinv Hst Hbe Hrt
    -- (keepfix, route (i)) the state is loaded: no load of a non-zero index
    ileft; ipureintro; exact stLoaded_self_k0 γ st hld
  iintro ⟨Hst, Hbe, Hrt⟩
  (try wp_auto)
  -- the applying index is above `ci`: set it
  wp_if_destruct
  · iunfold batchLockInv at HL
    icases HL with ⟨%mm, Hmt, HTM, Htok, #Hreg⟩
    have hlst : (stLoaded γ st).pending = false ∧ i = (stLoaded γ st).p + 1 := by
      unfold stLoaded; split <;> exact ⟨hp, hi⟩
    wp_apply_core (wp_ci_hookSet (Rw := TRow.triv) hS (srvCITriple0 cl) γ ci (stLoaded γ st) i t rt hlst.1
        hlst.2 (by unfold stLoaded; split <;> exact hlt)) $$ [Hst Htok Hrt] [HΦ Hmt HTM Happ Hbe]
    · iframe Hcipkg Hci Hinv Hst Htok Hrt
      -- (keepfix (c)) the applying triple's predicate, the caller's
      iright; iexact HP
    iintro Hst Hrt
    (try wp_auto)
    iapply HΦ
    iframe Happ Hbe Hrt
    isplitl [Hmt HTM]
    · iunfold hookDone; iexists mm; iframe; iexact Hreg
    have hw : { stLoaded γ st with k := i, pending := true } = { st with k := i, pending := true } := by
      unfold stLoaded; split <;> rfl
    rw [hw] at *
    iexact Hst
  · exfalso; exact Hif hce

end proof

end EtcdGrove
end Perennial
