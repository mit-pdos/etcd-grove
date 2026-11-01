/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Main.lean`. Lean-first (no Rocq
counterpart).

`Run` is specified at any storage registry (`∀ [KvrStor GF]`): the proof allocates the registry
(`kvrStorInv_alloc`, from the authority of an empty ghost map, as kv's `kvStorInv_alloc`) and
instantiates it there. `RandomConfig()` gives options a cluster may run with and 4 clients of 100
operations; `lintest.CounterClock()` a clock (its invariant at `kvrClockN`, apart from the driver's
`lintestN`); `Run` then answers `Ok`, so the panic branch is not taken, and hands back the cluster
with the stopper's token, which `Stop` takes. `receiptBound GF ≤ 2^63` gives `Run`'s `≤ 2^64 - 2`
and the clock's.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Run
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.RandomConfig
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster__Stop
public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.CounterClock

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The namespace of `Main`'s clock's invariant. -/
abbrev kvrClockN : Namespace := nroot.@"kvreconf_clock"

theorem lintestN_kvrClockN : (↑lintest.lintestN : CoPset) ⊆ ⊤ \ ↑kvrClockN :=
  mask_ndot_ne' nroot "lintest" "kvreconf_clock" (by decide)

section alloc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [KvrStor GF]

/-- The storage registry's invariant, with no storage registered yet. -/
theorem kvrStorInv_alloc (E : CoPset) :
    ⊢ ghostMapAuth (KvrStor.kvrStorName (GF := GF)) 1 (∅ : GMap Loc KvrStorRecT) ={E}=∗
      kvrStorInv (GF := GF) := by
  iintro Ha
  unfold kvrStorInv
  iapply inv_alloc
  inext
  unfold kvrStorInvBody
  iexists ∅
  iframe Ha
  iapply BigSepM.bigSepM_empty.2
  itrivial

end alloc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]

theorem Main.wp_proof
    (wp_RandomConfig : RandomConfig.spec (GF := GF) (hG := hG))
    (wp_CounterClock : lintest.CounterClock.spec (GF := GF) (hG := hG))
    (wp_Run : ∀ [KvrStor GF], Run.spec (GF := GF) (hG := hG))
    (wp_Stop : ∀ [KvrStor GF], Cluster.Stop.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro Hrb
  wp_start as #Hcc
  -- the storage registry
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := KvrStorRecT) with ⟨%γreg, Hreg⟩
  letI : KvrStor GF := ⟨γreg⟩
  imod kvrStorInv_alloc (GF := GF) ⊤ $$ Hreg with #HstorInv
  try wp_auto
  wp_apply wp_RandomConfig as %cfg %Hcfg
  obtain ⟨Hopts, Hcl, Hops, Hp1, Hp3⟩ := Hcfg
  ihave #Hlpkg : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest
    $$ []
  · iPkgInit
  wp_apply wp_CounterClock kvrClockN Hrb as %f ⟨%clockVal, #Hclk, Ht0⟩
  wp_apply wp_Run cfg clockVal (W64 0) ↑kvrClockN f Hopts (by omega) lintestN_kvrClockN
    (by rw [Hcl]; decide) (by rw [Hcl]; decide) (by rw [Hops]; decide)
    (by rw [Hcl, Hops]; decide) (by omega) $$ [Ht0]
    as %res %c ⟨%Hres, %γr, %vs, #Hcl, Hstp⟩
  · iframe
    iframe #
  subst Hres
  try wp_auto
  wp_apply wp_Stop γr vs c $$ [$Hcl $Hstp]
  try wp_auto
  iapply HΦ
  itrivial

end proof

end kvreconf
end EtcdGrove
end Perennial
