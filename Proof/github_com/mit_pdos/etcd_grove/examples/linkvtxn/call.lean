/-
Lean-first (no Rocq counterpart).

The proof of `call`: one branch per kind, the kind's function (`callGet`, `callList`, `callPut`,
`callDel`, `callTxn`), whose output is the model's answer at a good state (`Reply.lean`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.call
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.callGet
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.callList
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.callPut
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.callDel
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.callTxn
public import Perennial.Proof.context.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.linkvtxn go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

theorem call.wp_proof (wp_callGet : callGet.spec (GF := GF) (hG := hG))
    (wp_callList : callList.spec (GF := GF) (hG := hG))
    (wp_callPut : callPut.spec (GF := GF) (hG := hG))
    (wp_callDel : callDel.spec (GF := GF) (hG := hG))
    (wp_callTxn : callTxn.spec (GF := GF) (hG := hG)) :
    call.spec (GF := GF) (hG := hG) := by
  intro _ cl ms V hAs x i Q hx hgen
  wp_start as ⟨#Hcl, #Hone, #Hregs, Hau⟩
  wp_auto
  unfold callUpd callRes
  rcases decIn_cases x i hx with ⟨hk, rfl⟩ | ⟨hk, rfl⟩ | ⟨hk, rfl⟩ | ⟨hk, rfl⟩ |
    ⟨hk, cs, t, e, rfl, hcs, ht, he⟩
  · -- a get
    simp only [linkv.MIn.isWrite, Bool.false_eq_true, ↓reduceIte]
    wp_if_destruct
    · ihave #Hau' := readUpds_box ms Q $$ Hau
      wp_apply wp_callGet cl ms V hAs x.Key' Q $$ [] as %y Hy
      · iframe #
      iapply HΦ
      icases Hy with (%Hy | ⟨%σ, #HQ, %Hy, %Hb⟩)
      · ileft; ipureintro; exact Hy
      · iright
        iexists σ
        iframe HQ
        ipureintro
        refine ⟨?_, by omega, fun hg => ?_⟩
        · rw [Hy]; unfold getOut; split <;> rfl
        · rw [Hy]; exact getOut_eq σ hg.1 x.Key'
    · exact absurd hk Hif
  · -- a list
    simp only [linkv.MIn.isWrite, Bool.false_eq_true, ↓reduceIte]
    wp_if_destruct
    · exfalso; rw [hk] at Hif; exact absurd Hif (by decide)
    wp_if_destruct
    · ihave #Hau' := readUpds_box ms Q $$ Hau
      wp_apply wp_callList cl ms V hAs Q $$ [] as %y Hy
      · iframe #
      iapply HΦ
      icases Hy with (%Hy | ⟨%σ, #HQ, %Hy, %Hb⟩)
      · ileft; ipureintro; exact Hy
      · iright
        iexists σ
        iframe HQ
        ipureintro
        refine ⟨?_, by omega, fun hg => ?_⟩
        · rw [Hy]; rfl
        · rw [Hy]; exact listOut_eq σ hg
    · exact absurd hk Hif
  · -- a put
    simp only [linkv.MIn.isWrite, ↓reduceIte]
    wp_if_destruct
    · exfalso; rw [hk] at Hif; exact absurd Hif (by decide)
    wp_if_destruct
    · exfalso; rw [hk] at Hif; exact absurd Hif (by decide)
    wp_if_destruct
    · wp_apply wp_callPut cl ms V hAs x.Key' x.Val' Q $$ [Hau] as %y Hy
      · iframe #
        iExactEq Hau; rfl
      iapply HΦ
      icases Hy with (%Hy | ⟨%σ, HQ, %Hy, %Hb⟩)
      · ileft; ipureintro; exact Hy
      · iright
        iexists σ
        iframe HQ
        ipureintro
        refine ⟨?_, by omega, fun _ => ?_⟩
        · rw [Hy]; rfl
        · rw [Hy]; exact putOut_eq σ x.Key' x.Val'
    · exact absurd hk Hif
  · -- a delete
    simp only [linkv.MIn.isWrite, ↓reduceIte]
    wp_if_destruct
    · exfalso; rw [hk] at Hif; exact absurd Hif (by decide)
    wp_if_destruct
    · exfalso; rw [hk] at Hif; exact absurd Hif (by decide)
    wp_if_destruct
    · exfalso; rw [hk] at Hif; exact absurd Hif (by decide)
    wp_if_destruct
    · wp_apply wp_callDel cl ms V hAs x.Key' Q $$ [Hau] as %y Hy
      · iframe #
        iExactEq Hau; rfl
      iapply HΦ
      icases Hy with (%Hy | ⟨%σ, HQ, %Hy, %Hb⟩)
      · ileft; ipureintro; exact Hy
      · iright
        iexists σ
        iframe HQ
        ipureintro
        refine ⟨?_, by omega, fun hg => ?_⟩
        · rw [Hy]; rfl
        · rw [Hy]; exact delOut_eq σ hg x.Key'
    · exact absurd hk Hif
  · -- a transaction
    have hne := hgen.2 cs t e hx
    wp_if_destruct
    · exfalso; rw [hk] at Hif; exact absurd Hif (by decide)
    wp_if_destruct
    · exfalso; rw [hk] at Hif; exact absurd Hif (by decide)
    wp_if_destruct
    · exfalso; rw [hk] at Hif; exact absurd Hif (by decide)
    wp_if_destruct
    · exfalso; rw [hk] at Hif; exact absurd Hif (by decide)
    wp_apply wp_callTxn cl ms V hAs x cs t e Q hx hne $$ [Hau] as %y Hy
    · iframe #
      unfold callUpd
      iexact Hau
    iapply HΦ
    icases Hy with (%Hy | ⟨%σ, HQ, %Hy, %Hb⟩)
    · ileft; ipureintro; exact Hy
    · iright
      iexists σ
      unfold callRes
      iframe HQ
      ipureintro
      refine ⟨?_, Hb, fun hg => ?_⟩
      · rw [Hy]; rfl
      · rw [Hy, ← txnResOut_eq σ hg cs t e]
        split
        · rfl
        · rename_i hw
          rw [kvOpStep_read_rev σ hg _ (by simpa using hw)]
          rfl
end proof

end linkvtxn
end EtcdGrove
end Perennial
