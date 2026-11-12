/-
Lean-first (no Rocq counterpart). Trace-check's layer D, S7 (part 1) (2026-11-11): the proof of
`Main`, over its callees' specs.

`RunConcurrent(DefaultCConfig())` returns the cluster with a nil error and the run over
(`runOver`); `c.Events()` runs its view shift at the recorded trace `L`, giving `RunOk L` and, from
the recorder's receipts, `traceLenFits GF L` under `tcRunFits GF`, `L.length < 2^61 = numBound`; `mainPure_of_runOk` then
gives `ConvertEvents`' premise (ASCII), `NewTrace`'s (the events bounded, fewer than `numBound`, the
bootstrap logs), `newTrace`'s success at `t` (so `NewTrace`'s error is nil), `CheckTrace`'s premise
`t.CheckTraceOk true`, and the search's only result `{ ok := true }`, whose `TLCOK` is `true`: no
panic branch is taken.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.DefaultCConfig
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.RunConcurrent
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Cluster__Events
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.ConvertEvents
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.NewTrace
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.CheckTrace
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Result__TLCOK

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceCheck

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- `DefaultCConfig()` is a workload of the closed theorem. -/
theorem workload_defaultCConfig [GooseExts] : Workload defaultCConfig := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩ <;> (unfold defaultCConfig; simp only; word)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.Assumptions]

theorem Main.wp_proof
    (wp_DefaultCConfig : DefaultCConfig.spec (GF := GF) (hG := hG))
    (wp_RunConcurrent : RunConcurrent.spec (GF := GF) (hG := hG))
    (wp_Events : Cluster.Events.spec (GF := GF) (hG := hG))
    (wp_ConvertEvents : ConvertEvents.spec (GF := GF) (hG := hG))
    (wp_NewTrace : Etcdraft.NewTrace.spec (GF := GF) (hG := hG))
    (wp_CheckTrace : Etcdraft.CheckTrace.spec (GF := GF) (hG := hG))
    (wp_TLCOK : Etcdraft.Result.TLCOK.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro _ Hrb boot Hbf
  wp_start as ⟨#Hcc, #Hprem⟩
  ihave #Hed : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft $$ []
  · iPkgInit
  wp_apply wp_DefaultCConfig
  wp_apply (wp_RunConcurrent Hrb boot Hbf defaultCConfig workload_defaultCConfig) $$ [Hcc Hprem]
    as %c Hrun
  · iframe Hcc Hprem
  iunfold runOver at Hrun
  icases Hrun with ⟨%γt, %r, #Hc, #Hr, Hvs⟩
  try wp_auto
  wp_apply wp_Events c γt r (fun L => iprop(⌜RunOk L⌝)) $$ [Hvs] as %sl ⟨%L, #Hsl, %Hlen, %Hok⟩
  · iframe Hc Hr Hvs
  have hlen : (L.length : Int) < Etcdraft.numBound := by
    have := Hlen.lt_numBound Hrb; unfold Etcdraft.numBound; omega
  obtain ⟨hasc, hb, hl, hbl, t, hnt, hck, hres, -⟩ := mainPure_of_runOk L Hok hlen
  wp_apply wp_ConvertEvents sl L $$ [Hsl] as %out #Hout
  · iframe Hsl
    ipureintro; exact hasc
  wp_apply wp_NewTrace out (L.map TraceSim.evConv) $$ [Hout] as %tp %err Hres
  · iframe Hout
    ipureintro; exact ⟨hb, hl, hbl⟩
  rw [hnt]
  icases Hres with ⟨%Herr, #Htr⟩
  subst Herr
  wp_auto
  wp_apply wp_CheckTrace tp t true $$ [Htr] as %res ⟨%lr, %Hrel, %Hrr⟩
  · iframe Htr
    ipureintro; exact hck
  have hlr := hres lr Hrel
  subst hlr
  wp_apply wp_TLCOK res { ok := true }
  · ipureintro; exact Hrr
  have htlc : ({ ok := true } : Etcdraft.Result).tlcOK = true := rfl
  rw [htlc]
  wp_auto
  iapply HΦ
  itrivial

end proof

end TraceCheck
end EtcdGrove
end Perennial
