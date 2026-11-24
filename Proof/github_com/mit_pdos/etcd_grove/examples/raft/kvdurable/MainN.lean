/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurable/MainN.lean`. Lean-first (no Rocq
counterpart; 2026-11-16, kvraftN): `Main.lean`'s, from `RandomConfigN(k)`, the files of the ids
`1 … k + 4` claimed (`kdFileNamesM_nodup`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvdurable.MainN
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvdurable.RandomConfigN
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvdurable.Main

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem MainN.wp_proof
    (wp_RandomConfigN : RandomConfigN.spec (GF := GF) (hG := hG))
    (wp_CounterClock : lintest.CounterClock.spec (GF := GF) (hG := hG))
    (wp_Run : ∀ [KdStor GF], Run.spec (GF := GF) (hG := hG))
    (wp_Stop : ∀ [KdStor GF], Cluster.Stop.spec (GF := GF) (hG := hG)) :
    MainN.spec (GF := GF) (hG := hG) := by
  intro dir fs k Hrb Hfs
  wp_start as ⟨#Hcc, Hown⟩
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
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := KdStorRecT) with ⟨%γreg, Hreg⟩
  letI : KdStor GF := ⟨γreg⟩
  imod kdStorInv_alloc (GF := GF) ⊤ $$ Hreg with #HstorInv
  -- the files: every replica's in `dir` claimed, absent
  imod durableFiles_alloc (GF := GF) kdFilesN ⊤ fs
    ((raft_kvreconf.bootVoters (uint.nat k + 4)).map (kdFileName dir))
    (kdFileNamesM_nodup dir _ (by word)) $$ Hown with ⟨%γf, #Hfiles, Hfs'⟩
  rw [BigSepL.bigSepL_map]
  ihave Hfs' := (BigSepL.bigSepL_mono (Φ := fun _ i => dfile (GF := GF) γf (kdFileName dir i)
      (fs !! kdFileName dir i)) (Ψ := fun _ i => dfile (GF := GF) γf (kdFileName dir i) none)
      (fun {_ i} hk => by rw [Hfs i (List.mem_of_getElem? hk)])) $$ Hfs'
  try wp_auto
  wp_apply (wp_RandomConfigN k Hk1 Hk) as %cfg %Hcfg
  obtain ⟨Hopts, -, Hmax, Hcl, Hops, Hp1, Hp3⟩ := Hcfg
  ihave Hfs' : iprop([∗list] i ∈ raft_kvreconf.bootVoters (uint.nat cfg.Options'.MaxReplicas'),
      dfile (GF := GF) γf (kdFileName dir i) none) $$ [Hfs']
  · rw [Hmax, show uint.nat (k + W64 4) = uint.nat k + 4 by word]; iexact Hfs'
  ihave #Hlpkg : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.lintest
    $$ []
  · iPkgInit
  wp_apply wp_CounterClock kdClockN (by omega) as %f ⟨%clockVal, #Hclk, Ht0⟩
  wp_apply wp_Run cfg clockVal (W64 0) ↑kdClockN f dir γf Hopts Hrb lintestN_kdClockN
    (by rw [Hcl]; decide) (by rw [Hcl]; decide) (by rw [Hops]; decide)
    (by rw [Hcl, Hops]; decide) (by omega) $$ [Ht0 Hfs']
    as %res %c ⟨%Hres, %γr, %vs, Hcl, Hcr⟩
  · iframe
    iframe #
  subst Hres
  try wp_auto
  wp_apply wp_Stop γr vs dir c $$ [$Hcl $Hcr]
  try wp_auto
  iapply HΦ
  itrivial

end proof

end raft_kvdurable
end EtcdGrove
end Perennial
