/-
Lean-first (no Rocq counterpart).

The proof of `Check` (the partition plan's S3a, 2026-10-20; over linkvtxn's workload since
2026-10-20): linkvtxn's (`Proof/.../linkvtxn/Check.lean`, whose clock namespace and disjointness
lemmas it reuses) with the closure
`func(input any) any { return Apply(clis, input) }` meeting `applySpec` from linkv3p's
`Apply.spec` over the slice of clients.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.Check
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkv3p.Apply
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Gen
public import Spec.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Model
public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.Run
public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.CounterClock
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Check

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3p.Assumptions]

theorem Check.wp_proof
    (wp_Run : lintest.Run.spec (GF := GF) (hG := hG))
    (wp_CounterClock : lintest.CounterClock.spec (GF := GF) (hG := hG))
    (wp_Model : linkvtxn.Model.spec (GF := GF) (hG := hG))
    (wp_Gen : linkvtxn.Gen.spec (GF := GF) (hG := hG))
    (wp_Apply : Apply.spec (GF := GF) (hG := hG)) :
    Check.spec (GF := GF) (hG := hG) := by
  intro _ CRE CEC γ cls clis clients ops dur hAs Hrb hne H0 H31 Hops Hmul
  wp_start as ⟨#Hcc, #Hcls, #Hok, Hst⟩
  wp_auto
  ipersist clis
  ihave #Plkv : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkvtxn
      $$ []
  · iPkgInit
  ihave #Plt : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest
      $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #HA := wp_Apply γ cls clis hAs hne $$ Hpkg Plkv Pcli Hcls Hok
  wp_apply wp_Model as %m ⟨%Hp, #Hinit, %Hsc, #Hstep, #Heh⟩
  ihave #Hm := isModel_of_step linkvtxn.linkvtxnS m $$ [Hinit Hstep Heh]
  · iframe Hinit Hstep Heh
    ipureintro; exact ⟨Hp, Hsc⟩
  wp_apply wp_CounterClock linkvtxn.clockN Hrb as %clock ⟨%clockVal, #Hclk, Hc0⟩
  wp_apply wp_Run (linkv.PSet linkvtxn.MS linkvtxn.MI) linkvtxn.linkvtxnS m _ _ clock
    linkvtxn.linkvInOk (linkvtxn.linkvState γ) clockVal (W64 0) linkvtxn.linkvE ↑linkvtxn.clockN
    clients ops dur linkvtxn.lintestN_linkvE linkvtxn.lintestN_clockN H0 H31 Hops Hmul
    $$ [Hst Hc0]
  · iframe Hc0 Hcc Hm Hclk
    isplitr
    · -- the closure: `Apply`'s update, passed through its return
      unfold lintest.applySpec
      iintro %i
      imodintro
      iintro %Φ' ⟨Hin, Htt⟩ HAU
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
      ihave HQ := HQ $$ [$Hio $Htt]
      wp_auto
      iexact HQ
    isplitr
    · iapply wp_Gen
    · iExactEq Hst; rfl
  iintro %r %Hr
  wp_auto
  iapply HΦ
  ipureintro; exact Hr

end proof

end linkv3p
end EtcdGrove
end Perennial
