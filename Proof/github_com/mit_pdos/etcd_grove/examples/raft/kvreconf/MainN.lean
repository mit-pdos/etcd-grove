/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvreconf/MainN.lean`. Lean-first (no Rocq
counterpart; 2026-11-16, kvraftN): `Main.lean`'s, from `RandomConfigN(k)`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.MainN
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Run
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.RandomConfigN
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Cluster__Stop
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.lintest.CounterClock

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The namespace of `Main`'s clock's invariant. -/
abbrev kvrClockNk : Namespace := nroot.@"kvreconf_clockN"

theorem lintestN_kvrClockNk : (↑lintest.lintestN : CoPset) ⊆ ⊤ \ ↑kvrClockNk :=
  mask_ndot_ne' nroot "lintest" "kvreconf_clockN" (by decide)

section alloc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Assumptions]
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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Assumptions]

theorem MainN.wp_proof
    (wp_RandomConfigN : RandomConfigN.spec (GF := GF) (hG := hG))
    (wp_CounterClock : lintest.CounterClock.spec (GF := GF) (hG := hG))
    (wp_Run : ∀ [KvrStor GF], Run.spec (GF := GF) (hG := hG))
    (wp_Stop : ∀ [KvrStor GF], Cluster.Stop.spec (GF := GF) (hG := hG)) :
    MainN.spec (GF := GF) (hG := hG) := by
  intro k Hrb
  wp_start as #Hcc
  try wp_auto
  -- the range check: `k` outside `[1, 1000]` returns at once
  wp_if_destruct
  · try wp_auto
    iapply HΦ
    itrivial
  wp_if_destruct
  · try wp_auto
    iapply HΦ
    itrivial
  have Hk1 : 1 ≤ uint.Z k := by word
  have Hk : uint.Z k < 2 ^ 59 := by word
  -- the storage registry
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := KvrStorRecT) with ⟨%γreg, Hreg⟩
  letI : KvrStor GF := ⟨γreg⟩
  imod kvrStorInv_alloc (GF := GF) ⊤ $$ Hreg with #HstorInv
  try wp_auto
  wp_apply (wp_RandomConfigN k Hk1 Hk) as %cfg %Hcfg
  obtain ⟨Hopts, -, Hcl, Hops, Hp1, Hp3⟩ := Hcfg
  ihave #Hlpkg : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.lintest
    $$ []
  · iPkgInit
  wp_apply wp_CounterClock kvrClockNk (by omega) as %f ⟨%clockVal, #Hclk, Ht0⟩
  wp_apply wp_Run cfg clockVal (W64 0) ↑kvrClockNk f Hopts (by omega) lintestN_kvrClockNk
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

end raft_kvreconf
end EtcdGrove
end Perennial
