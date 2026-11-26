/-
The proof of `Spec/os/CrashStILA.lean`: `syscall.Fdatasync`'s model over `wp_osFsync_L` with the
accessor whose value follows the state (`csI_accA`: `a` at the state before, `a'` at the synced
one); when the sync leaves the state as it was, the value moves first (`csOwnIL_setA`, the synced
state being the state). Lean-first (no Rocq counterpart).
-/
module

public import Spec.os.CrashStILA
public import Proof.os.CrashStILA
public import Spec.os.CrashStILR

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

open Classical in
theorem syscall.Fdatasync.wp_proof_crashILA [syscall.Assumptions] :
    syscall.Fdatasync.specCrashILA (GF := GF) (hG := hG) := by
  intro A _ fd dq d N i γ γa γc Ok a a' m bs c hi hN hcov hok
  subst hi
  wp_start as ⟨#Hos, #Hinv, Hfd, Hown, Hb⟩
  imod csOwnIL_ok N d.ino γ γa γc Ok _ a ⊤ CoPset.subseteq_top $$ Hinv Hown with ⟨Hown, %Hok0⟩
  by_cases heq : csSynced m [] [] bs 0 0 = (⟨m, bs, 0, 0, .idle⟩ : CSt)
  · -- the sync leaves the state: the value moves first
    imod csOwnIL_setA N d.ino γ γa γc Ok _ a a' ⊤ CoPset.subseteq_top (by rw [← heq]; exact hok)
      $$ Hinv Hown with Hown
    wp_apply wp_osFsync_L fd dq d N (csInvI (GF := GF) N d.ino γ γa γc Ok) (csTokI γ γa a') (Ok a')
      (csI_acc N d.ino γ γa γc Ok a') m bs c hN hcov hok $$ Hos Hinv Hfd Hown Hb as %e Hr Hfd
    icases Hr with (⟨%he, H⟩ | ⟨%he, Hown, Hb⟩)
    · iapply wp_errno
      iapply HΦ
      iframe Hfd
      ileft; iframe; ipureintro; exact he
    · imod csOwnIL_setA N d.ino γ γa γc Ok _ a' a ⊤ CoPset.subseteq_top Hok0.1 $$ Hinv Hown with Hown
      iapply wp_errno
      iapply HΦ
      iframe Hfd
      iright; iframe; ipureintro; exact ⟨he.1, he.2.2⟩
  · -- the value follows the state
    have hne : ¬ ((⟨m, bs, 0, 0, .idle⟩ : CSt) = csSynced m [] [] bs 0 0) := fun h => heq h.symm
    let av : CSt → A := fun s => if s = csSynced m [] [] bs 0 0 then a' else a
    have h0 : av ⟨m, bs, 0, 0, .idle⟩ = a := if_neg hne
    have h1 : av (csSynced m [] [] bs 0 0) = a' := if_pos rfl
    ihave Hown := csOwnL_tok (csTokI γ γa a) (fun s => csTokI γ γa (av s) s) d.ino _
      (by show _ = csTokI γ γa (av _) _; rw [h0]) $$ Hown
    wp_apply wp_osFsync_L fd dq d N (csInvI (GF := GF) N d.ino γ γa γc Ok)
      (fun s => csTokI γ γa (av s) s) (fun s => Ok (av s) s)
      (csI_accA N d.ino γ γa γc Ok av) m bs c hN hcov (by show Ok (av _) _; rw [h1]; exact hok)
      $$ Hos Hinv Hfd Hown Hb as %e Hr Hfd
    iapply wp_errno
    iapply HΦ
    iframe Hfd
    icases Hr with (⟨%he, Hown, Hb⟩ | ⟨%he, Hown, Hb⟩)
    · ihave Hown := csOwnL_tok (fun s => csTokI γ γa (av s) s) (csTokI γ γa a') d.ino _
        (by show csTokI γ γa (av _) _ = _; rw [h1]) $$ Hown
      ileft; iframe; ipureintro; exact he
    · ihave Hown := csOwnL_tok (fun s => csTokI γ γa (av s) s) (csTokI γ γa a) d.ino _
        (by show csTokI γ γa (av _) _ = _; rw [h0]) $$ Hown
      iright; iframe; ipureintro; exact ⟨he.1, he.2.2⟩

open Classical in
/-- `syscall.Fdatasync.wp_proof_crashILA` over `csInvIR` (the client resource the same at both
values). -/
theorem syscall.Fdatasync.wp_proof_crashILAR [syscall.Assumptions] :
    syscall.Fdatasync.specCrashILAR (GF := GF) (hG := hG) := by
  intro A _ fd dq d N i γ γa γc Ok R _ a a' m bs c hi hN hcov hok hR
  subst hi
  wp_start as ⟨#Hos, #Hinv, Hfd, Hown, Hb⟩
  imod csOwnILR_ok R N d.ino γ γa γc Ok _ a ⊤ CoPset.subseteq_top $$ Hinv Hown with ⟨Hown, %Hok0⟩
  by_cases heq : csSynced m [] [] bs 0 0 = (⟨m, bs, 0, 0, .idle⟩ : CSt)
  · -- the sync leaves the state: the value moves first
    imod csOwnILR_upd R N d.ino γ γa γc Ok _ a a' ⊤ CoPset.subseteq_top
      (fun _ => by rw [← heq]; exact hok) iprop(emp) $$ Hinv Hown [] with ⟨Hown, -⟩
    · iintro HR; imodintro; isplitl
      · iapply hR.1 $$ HR
      · iempintro
    wp_apply wp_osFsync_L fd dq d N (csInvIR (GF := GF) N d.ino γ γa γc Ok R) (csTokI γ γa a') (Ok a')
      (csI_accR R N d.ino γ γa γc Ok a') m bs c hN hcov hok $$ Hos Hinv Hfd Hown Hb as %e Hr Hfd
    icases Hr with (⟨%he, H⟩ | ⟨%he, Hown, Hb⟩)
    · iapply wp_errno
      iapply HΦ
      iframe Hfd
      ileft; iframe; ipureintro; exact he
    · imod csOwnILR_upd R N d.ino γ γa γc Ok _ a' a ⊤ CoPset.subseteq_top (fun _ => Hok0.1)
        iprop(emp) $$ Hinv Hown [] with ⟨Hown, -⟩
      · iintro HR; imodintro; isplitl
        · iapply hR.2 $$ HR
        · iempintro
      iapply wp_errno
      iapply HΦ
      iframe Hfd
      iright; iframe; ipureintro; exact ⟨he.1, he.2.2⟩
  · -- the value follows the state
    have hne : ¬ ((⟨m, bs, 0, 0, .idle⟩ : CSt) = csSynced m [] [] bs 0 0) := fun h => heq h.symm
    let av : CSt → A := fun s => if s = csSynced m [] [] bs 0 0 then a' else a
    have h0 : av ⟨m, bs, 0, 0, .idle⟩ = a := if_neg hne
    have h1 : av (csSynced m [] [] bs 0 0) = a' := if_pos rfl
    have hRav : ∀ s s', R (av s) ⊢ R (av s') := by
      intro s s'
      by_cases h : s = csSynced m [] [] bs 0 0 <;> by_cases h' : s' = csSynced m [] [] bs 0 0 <;>
        simp only [av, h, h', if_true, if_false] <;>
        first | exact .rfl | exact hR.1 | exact hR.2
    ihave Hown := csOwnL_tok (csTokI γ γa a) (fun s => csTokI γ γa (av s) s) d.ino _
      (by show _ = csTokI γ γa (av _) _; rw [h0]) $$ Hown
    wp_apply wp_osFsync_L fd dq d N (csInvIR (GF := GF) N d.ino γ γa γc Ok R)
      (fun s => csTokI γ γa (av s) s) (fun s => Ok (av s) s)
      (csI_accAR R N d.ino γ γa γc Ok av hRav) m bs c hN hcov (by show Ok (av _) _; rw [h1]; exact hok)
      $$ Hos Hinv Hfd Hown Hb as %e Hr Hfd
    iapply wp_errno
    iapply HΦ
    iframe Hfd
    icases Hr with (⟨%he, Hown, Hb⟩ | ⟨%he, Hown, Hb⟩)
    · ihave Hown := csOwnL_tok (fun s => csTokI γ γa (av s) s) (csTokI γ γa a') d.ino _
        (by show csTokI γ γa (av _) _ = _; rw [h1]) $$ Hown
      ileft; iframe; ipureintro; exact he
    · ihave Hown := csOwnL_tok (fun s => csTokI γ γa (av s) s) (csTokI γ γa a) d.ino _
        (by show csTokI γ γa (av _) _ = _; rw [h0]) $$ Hown
      iright; iframe; ipureintro; exact ⟨he.1, he.2.2⟩

end proof

end EtcdGrove
end Perennial
