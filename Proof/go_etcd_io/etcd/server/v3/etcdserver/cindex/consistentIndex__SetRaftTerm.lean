/-
Proof of `Spec/consistentIndex__SetRaftTerm.lean` (keepfix (c)). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__SetRaftTerm

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

theorem consistentIndex.SetRaftTerm.wp_proof :
    consistentIndex.SetRaftTerm.spec (GF := GF) (hG := hG) := by
  intro ci γ P rt r
  wp_start as ⟨#Hci, Hrt, #Hmono⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  unfold isCI
  icases Hci with ⟨-, -, #Hpmu⟩
  (try wp_auto)
  wp_apply sync.Mutex.wp_Lock $$ [$Hpmu] as ⟨Hlocked, HL⟩
  iunfold ciPairInv at HL
  icases HL with ⟨%kl, %tl, %rtl, Hpk, Hterm, Hrtf, Hrtg, #HP⟩
  iunfold ciRaftTerm at Hrt
  icombine Hrt Hrtg gives %Heqr
  obtain ⟨_, rfl⟩ := Heqr
  -- raise the field and both halves of its mirror to `rtMax rt r`
  imod ghostVar_update_halves (rtMax rt r) $$ Hrt Hrtg with ⟨Hrt, Hrtg⟩
  ihave #HP' : iprop(⌜kl = W64 0⌝ ∨ □ P kl tl (rtMax rt r)) $$ [HP]
  · icases HP with (%H0 | #HP)
    · ileft; ipureintro; exact H0
    · iright; iintro !>; iapply Hmono $$ HP
  (try wp_auto)
  wp_if_destruct
  · (try wp_auto)
    have hm : rtMax rt r = r := by unfold rtMax; rw [if_pos (by word)]

    rw [hm]
    wp_apply sync.Mutex.wp_Unlock $$ [$Hpmu $Hlocked Hpk Hterm Hrtf Hrtg]
    · inext; iunfold ciPairInv; iexists kl, tl, r; iframe Hpk Hterm Hrtf Hrtg HP'
    iapply HΦ
    iunfold ciRaftTerm
    iexact Hrt
  · (try wp_auto)
    have hm : rtMax rt r = rt := by unfold rtMax; rw [if_neg (by word)]

    rw [hm]
    wp_apply sync.Mutex.wp_Unlock $$ [$Hpmu $Hlocked Hpk Hterm Hrtf Hrtg]
    · inext; iunfold ciPairInv; iexists kl, tl, rt; iframe Hpk Hterm Hrtf Hrtg HP'
    iapply HΦ
    iunfold ciRaftTerm
    iexact Hrt

end proof

end EtcdGrove
end Perennial
