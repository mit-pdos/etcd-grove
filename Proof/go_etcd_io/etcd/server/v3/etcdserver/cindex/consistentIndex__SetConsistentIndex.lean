/-
Proof of `Spec/consistentIndex__SetConsistentIndex.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__SetConsistentIndex

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.cindex

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.cindex.Assumptions]

theorem consistentIndex.SetConsistentIndex.wp_proof :
    consistentIndex.SetConsistentIndex.spec (GF := GF) (hG := hG) := by
  intro ci γ P v term rt
  wp_start as ⟨#Hci, Hrt, #HP⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  unfold isCI
  icases Hci with ⟨#Hinv, -, #Hpmu⟩
  (try wp_auto)
  -- (keepfix-d) the pair mutex: the term field and the index's second mirror
  wp_apply sync.Mutex.wp_Lock $$ [$Hpmu] as ⟨Hlocked, HL⟩
  iunfold ciPairInv at HL
  icases HL with ⟨%kl, %tl, %rtl, Hpk, Hterm, Hrtf, Hrtg, -⟩
  -- (keepfix (c)) the raft term field is the caller's mirror's
  iunfold ciRaftTerm at Hrt
  icombine Hrt Hrtg gives %Heqr
  obtain ⟨_, rfl⟩ := Heqr
  (try wp_auto)
  -- the index: the linearization point
  wp_apply_core sync.atomic.wp_StoreUint64 $$ [] [HΦ Hpk Hterm Hrt Hrtf Hrtg Hlocked defer ci term]
  · iPkgInit
  iinv Hinv with Hi Hclose
  imod HΦ with ⟨%k, Hk, HΦ⟩
  imodintro
  inext
  unfold ciInv
  icases Hi with ⟨%k0, Hidx, Hg, Hpk0⟩
  iexists k0
  iframe Hidx
  iintro Hidx
  unfold ciIdx
  imod ghostVar_update_halves v $$ Hk Hg with ⟨Hk, Hg⟩
  imod ghostVar_update_halves v $$ Hpk Hpk0 with ⟨Hpk, Hpk0⟩
  imod HΦ $$ Hk with HΦ
  imod Hclose $$ [Hidx Hg Hpk0] with -
  · inext; iexists v; iframe
  imodintro
  (try wp_auto)
  -- the term: owned under the pair mutex
  wp_apply_core sync.atomic.wp_StoreUint64 $$ [] [HΦ Hpk Hterm Hrt Hrtf Hrtg Hlocked defer]
  · iPkgInit
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists tl
  iframe Hterm
  iintro Hterm
  imod Hmask with -
  imodintro
  (try wp_auto)
  wp_apply sync.Mutex.wp_Unlock $$ [$Hpmu $Hlocked Hpk Hterm Hrtf Hrtg]
  · inext; iunfold ciPairInv; iexists v, term, rt; iframe Hpk Hterm Hrtf Hrtg HP
  iapply HΦ
  iunfold ciRaftTerm
  iexact Hrt

end proof

end EtcdGrove
end Perennial
