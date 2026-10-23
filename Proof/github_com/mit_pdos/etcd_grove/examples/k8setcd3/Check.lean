module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Check
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Model
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Gen
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Apply
public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.Run
public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.CounterClock

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output Obj item mstore mcfg state)

/-- The clock's namespace (`CounterClock`'s invariant). -/
def clockN : Namespace := nroot .@ "k8setcd3_clock"

/-- `lintest`'s namespace is not `Apply`'s mask's. -/
theorem lintestN_drvE : (↑lintest.lintestN : CoPset) ⊆
    ⊤ \ drvE := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff]
  refine ⟨CoPset.mem_full, fun h' => ?_⟩
  unfold drvE at h'
  simp only [Iris.Std.LawfulSet.mem_union] at h'
  rcases h' with ((h' | h') | h') | h'
  · exact ndot_ne_disjoint nroot (by decide : "lintest" ≠ "raft_commit") p ⟨hp, h'⟩
  · exact ndot_ne_disjoint nroot (by decide : "lintest" ≠ "server_kv") p ⟨hp, h'⟩
  · exact ndot_ne_disjoint nroot (by decide : "lintest" ≠ "k8sStore") p ⟨hp, h'⟩
  · exact ndot_ne_disjoint nroot (by decide : "lintest" ≠ "k8setcd3") p ⟨hp, h'⟩

/-- The clock's mask is not `lintest`'s. -/
theorem lintestN_clockN : (↑lintest.lintestN : CoPset) ⊆
    ⊤ \ ↑clockN := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h' =>
    ndot_ne_disjoint nroot (by decide : "lintest" ≠ "k8setcd3_clock") p ⟨hp, h'⟩⟩

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

theorem Check.wp_proof
    (wp_Run : lintest.Run.spec (GF := GF) (hG := hG))
    (wp_CounterClock : lintest.CounterClock.spec (GF := GF) (hG := hG))
    (wp_Model : Model.spec (GF := GF) (hG := hG))
    (wp_Gen : Gen.spec (GF := GF) (hG := hG))
    (wp_Apply : Apply.spec (GF := GF) (hG := hG)) :
    Check.spec (GF := GF) (hG := hG) := by
  intro _ _ _ γ sp c g0 s0 clients ops dur hc hpfx hrp hAs hne Hrb H0 H31 Hops Hmul Hg0
  wp_start as ⟨#Hcc, #Hst, #Hinvs, Hks, #Hs0⟩
  wp_auto
  ipersist s
  ihave #HA := (wp_Apply γ sp c g0 hc hpfx hrp hAs) $$ Hpkg Hpkg2 Hst Hinvs %hne
  wp_apply wp_Model s0 g0 $$ [] as %m ⟨%Hp, #Hinit, %Hsc, #Hstep, #Heh⟩
  · iframe #
    ipureintro; exact Hg0
  ihave #Hm := github_com.anishathalye.porcupine.isModel_of_step (k8setcd3S g0) m $$ [Hinit Hstep Heh]
  · iframe Hinit Hstep Heh
    ipureintro; exact ⟨Hp, Hsc⟩
  wp_apply wp_CounterClock clockN Hrb as %clock ⟨%clockVal, #Hclk, Hc0⟩
  wp_apply wp_Run (linkv.PSet GSt Input) (k8setcd3S g0) m _ _ clock kInOk (kState γ g0) clockVal
    (W64 0) drvE ↑clockN clients ops dur lintestN_drvE lintestN_clockN H0 H31 Hops Hmul
    $$ [Hks Hc0]
  · iframe Hc0 Hcc Hm Hclk
    isplitr
    · -- the closure: `Apply`'s update, passed through its return
      unfold lintest.applySpec
      iintro %i
      imodintro
      iintro %Φ' Hin HAU
      wp_auto
      wp_bind (App (App (Val _) (Val _)) (Val _))
      iapply HA $$ %i Hin
      inext
      imod HAU with ⟨%S, Hs, Hc⟩
      imodintro
      iexists S
      iframe Hs
      iintro %S' %o Hb
      imod Hc $$ Hb with HQ
      imodintro
      iintro Hio
      ihave HQ := HQ $$ Hio
      wp_auto
      iexact HQ
    isplitr
    · iapply wp_Gen
    · iExactEq Hks; rfl
  iintro %r %Hr
  wp_auto
  iapply HΦ
  ipureintro; exact Hr

end proof

end k8setcd3
end EtcdGrove
end Perennial
