module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.newWCache
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Check
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Model
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Gen
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Apply
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.lintest.RunLin2
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.lintest.CounterClock
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.failureFree
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.realCheck
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealGlue

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg state)

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem Check.wp_proof
    (wp_Run : lintest.RunLin2.spec (GF := GF) (hG := hG))
    (wp_CounterClock : lintest.CounterClock.spec (GF := GF) (hG := hG))
    (wp_Model : Model.spec (GF := GF) (hG := hG))
    (wp_newCache : newWCache.spec (GF := GF) (hG := hG))
    (wp_Gen : Gen.spec (GF := GF) (hG := hG))
    (wp_Apply : Apply.spec (GF := GF) (hG := hG))
    (wp_failureFree : failureFree.spec (GF := GF) (hG := hG))
    (wp_realCheck : realCheck.spec (GF := GF) (hG := hG)) :
    Check.spec (GF := GF) (hG := hG) := by
  intro _ _ _ γ sp c g0 γk s0 hsl hs clients ops watchers wops dur hc hpfx hrp hdi hvi hAs hse htb
    hnr hne Hrb H0 Hw0 H31 Hops Hwops Hmul Hg0 Hrv0 hrun0
  wp_start as ⟨#Hcc, #Hst, #Hrs, #Hinvs, Hks, #HinvK, #Hsw, #Hwl, #Hs0, #Hsl, #Hhs⟩
  ihave %Hs0rv : ⌜s0.rv' = g0.st.rv⌝ $$ [Hs0]
  · iunfold storeOwn at Hs0; icases Hs0 with ⟨-, %h⟩; ipureintro; exact h
  wp_auto
  have hf62 : uint.Z s0.rv' < 2 ^ 62 := by rw [Hs0rv]; have := Hrv0; have := Hg0; word
  wp_apply wp_newCache c clients (clients * ops) s0.rv' hf62 as %tbl ⟨#Htbl, #Hfl⟩
  (try wp_auto)
  ipersist s
  ipersist tbl
  ihave #HA := (wp_Apply γ sp tbl c g0 γk hc hpfx hrp hdi hvi hAs hse htb hnr Hrv0) $$ Hpkg Hpkg2 Hst
    Hinvs %hne Htbl Hrs HinvK Hsw Hwl
  wp_apply wp_Model s0 hsl hs g0 $$ [] as %m ⟨%Hp, #Hinit, %Hsc, #Hstep, #Heh⟩
  · iframe #
    ipureintro; exact ⟨Hg0, Hrv0⟩
  ihave #Hm := github_com.anishathalye.porcupine.isModel_of_step (k8setcd3S g0) m $$ [Hinit Hstep Heh]
  · iframe Hinit Hstep Heh
    ipureintro; exact ⟨Hp, Hsc⟩
  wp_apply wp_CounterClock clockN Hrb as %clock ⟨%clockVal, #Hclk, Hc0⟩
  wp_apply wp_Run (linkv.PSet HSt Input) (k8setcd3S g0) m _ _ clock (kInOk c g0.st.rv) (kState γ g0) clockVal
    (W64 0) drvE ↑clockN clients ops watchers wops dur lintestN_drvE lintestN_clockN H0 Hw0 H31 Hops
    Hwops Hmul
    $$ [Hks Hc0]
  · iframe Hc0 Hcc Hm Hclk
    isplitr
    · -- the closure: `Apply`'s update, passed through its return
      unfold lintest.applySpec
      iintro %i
      imodintro
      iintro %Φ' ⟨Hin, Htt⟩ HAU
      wp_auto
      wp_bind (App (App (App (Val _) (Val _)) (Val _)) (Val _))
      iapply HA $$ %i [Hin Htt]
      · iframe
      inext
      imod HAU with ⟨%S, Hs, Hc⟩
      imodintro
      iexists S
      iframe Hs
      iintro %S' %o Hb
      imod Hc $$ Hb with HQ
      imodintro
      iintro %o' Hio
      ihave HQ := HQ $$ %o' Hio
      wp_auto
      iexact HQ
    isplitr
    · -- the closure: `Gen` of the table, boxed
      unfold lintest.genSpec
      iintro %id
      imodintro
      iintro %Φ' %H0id HQg
      wp_auto
      wp_apply wp_Gen c tbl id s0.rv' $$ [] as %x ⟨%Hx, #Hcx⟩
      · iframe #
      (try wp_auto)
      iapply HQg
      imodintro
      iunfold kInOk
      iexists x
      iframe Hcx
      ipureintro; exact ⟨rfl, Hx.1, Hs0rv ▸ Hx.2⟩
    · iExactEq Hks; rfl
  iintro %r %lsl ⟨%Hr, Hok⟩
  wp_auto
  by_cases hr : r = go!"Ok"
  · subst hr
    ihave ⟨%lops, Hl, #Hio, %Hlops⟩ := Hok $$ %rfl
    obtain ⟨Hlen, Hlin, Hhist⟩ := Hlops
    ihave %Hbox := k8s_correctness.opsIoOk_boxes g0 lops $$ Hio
    simp only [decide_true, Bool.not_true]
    wp_auto
    wp_apply wp_failureFree lsl lops (DFrac.own 1) Hbox $$ [Hl] as %b ⟨Hl, %Hb⟩
    · iframe
    cases b
    · wp_auto
      iapply HΦ
      ipureintro; exact Hr
    · wp_auto
      have hbound : uint.nat g0.st.rv + lops.length < 2 ^ 63 := by
        have h1 : (lops.length : Int) < 2 ^ 60 := by rw [Hlen]; exact Hmul
        omega
      wp_apply wp_realCheck s0 g0 lsl lops dur Hlin Hhist (Hb.1 rfl) hrun0 hbound (by omega) $$ [Hl]
        as %r' %Hr'
      · iframe Hl Hcc Hs0 Hio
      iapply HΦ
      ipureintro; exact Hr'
  · simp only [hr, decide_false, Bool.not_false]
    wp_auto
    iapply HΦ
    ipureintro; exact Hr

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
