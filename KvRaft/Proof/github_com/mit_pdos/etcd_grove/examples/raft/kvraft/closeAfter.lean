/-
The proof of `closeAfter` (`KvRaft/Spec/.../kvraft/closeAfter.lean`): the timer's state `t` behind
its mutex, whose invariant holds `t.over` and, while it is `false`, the caller's `R`; the timer's
function (`time.AfterFunc`) and `disarm` each take the lock, take `R` if `over` is still `false`
and set it; the timer then closes `c` with `R` (`net.Conn.Close.spec`, through the caller's
accessor), `disarm` gives `R` back.
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.closeAfter
public import KvRaft.Spec.net.Conn__Close
public import Perennial.Proof.time.Link
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [package_sem' : net.Assumptions]

theorem closeAfter.wp_proof (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG)) :
    closeAfter.spec (GF := GF) (hG := hG) := by
  intro c cn s a d R
  unfold net.isConn
  wp_start as ⟨⟨%t, %la, %ra, %Hct, #Hc⟩, HR, #Hacc⟩
  subst Hct
  wp_auto
  irename «$r0» => Ht
  generalize «$r0_ptr» = tl at *
  iStructNamed Ht
  ipersist t
  ipersist c
  imod sync.init_Mutex (iprop(∃ ov : Bool,
      tl.[github_com.mit_pdos.etcd_grove.examples.raft.kvraft.connTimer, go!"over"] ↦ ov ∗
      (if ov then True else R))) ⊤ _ $$ mu [over HR] with #Hmu
  · inext
    iexists false
    iframe over
    simp only [Bool.false_eq_true, ↓reduceIte]
    iexact HR
  wp_apply time.wp_AfterFunc $$ [] as %tm -
  · -- the timer's function
    wp_auto
    wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
    icases HL with ⟨%ov, Hov, HRo⟩
    wp_auto
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hov]
    · inext
      iexists true
      iframe Hov
      simp only [↓reduceIte]
      itrivial
    cases ov
    · -- it fires: closes `c` with `R`
      (try wp_auto)
      wp_apply wp_Close t cn s a la ra (fun _ => iprop(True)) $$ [HRo] as %err ⟨%res, -, -⟩
      · iframe Hc
        simp only [Bool.false_eq_true, ↓reduceIte]
        iapply Hacc $$ HRo
      (try wp_auto)
      itrivial
    · (try wp_auto)
      itrivial
  (try wp_auto)
  iapply HΦ
  imodintro
  iintro %Φ' HΦ'
  wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  icases HL with ⟨%ov, Hov, HRo⟩
  wp_auto
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked Hov]
  · inext
    iexists true
    iframe Hov
    simp only [↓reduceIte]
    itrivial
  (try wp_auto)
  cases ov
  · rw [show (!false) = true from rfl]
    iapply HΦ' $$ %true
    simp only [↓reduceIte]
    iapply (show ((if false = true then iprop(True) else R : IProp GF) ⊢ R) by
      simp only [Bool.false_eq_true, ↓reduceIte]; exact .rfl) $$ HRo
  · rw [show (!true) = false from rfl]
    iapply HΦ' $$ %false
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial

end proof

end kvraft
end EtcdGrove
end Perennial
