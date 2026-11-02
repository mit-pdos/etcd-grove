/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Main.lean`. Lean-first (no Rocq
counterpart). kvreconf's, with the files.

The storage registry (`KdStor`, `kdStorInv`) and the files' invariant (`durableFiles_alloc`, from
the program's files, claiming every replica id's file in `dir`, absent) are allocated; then
`RandomConfig`, the counter clock, `Run` (which allocates the store's ghost state and gives the
crasher's token back) and `Stop` (which takes it).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Run
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.RandomConfig
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__Stop
public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.CounterClock

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The namespace of `Main`'s clock's invariant. -/
abbrev kdClockN : Namespace := nroot.@"kvdurable_clock"

theorem lintestN_kdClockN : (↑lintest.lintestN : CoPset) ⊆ ⊤ \ ↑kdClockN :=
  mask_ndot_ne' nroot "lintest" "kvdurable_clock" (by decide)

/-- The ids' decimal names (`itoa`'s), one digit each. -/
theorem allIds_decimal :
    kvreconf.allIds.map (fun i : w64 => decimalB (uint.nat i)) =
      [decimalB 1, decimalB 2, decimalB 3, decimalB 4, decimalB 5, decimalB 6, decimalB 7,
        decimalB 8, decimalB 9] := by
  rfl

/-- The replicas' files in `dir` are distinct names. -/
theorem kdFileNames_nodup (dir : GoString) :
    (kvreconf.allIds.map (kdFileName dir)).Nodup := by
  have Hd : (kvreconf.allIds.map (fun i : w64 => decimalB (uint.nat i))).Nodup := by
    have hdig : ∀ n, n < 10 → decimalB n = [W8 ((Nat.digitChar n).toNat : Int)] := fun n h => by
      unfold decimalB; rw [Nat.toDigits_of_lt_base h]; rfl
    rw [allIds_decimal]
    rw [hdig 1 (by decide), (Nat.digitChar_eq_one (n := 1)).2 rfl]
    rw [hdig 2 (by decide), (Nat.digitChar_eq_two (n := 2)).2 rfl]
    rw [hdig 3 (by decide), (Nat.digitChar_eq_three (n := 3)).2 rfl]
    rw [hdig 4 (by decide), (Nat.digitChar_eq_four (n := 4)).2 rfl]
    rw [hdig 5 (by decide), (Nat.digitChar_eq_five (n := 5)).2 rfl]
    rw [hdig 6 (by decide), (Nat.digitChar_eq_six (n := 6)).2 rfl]
    rw [hdig 7 (by decide), (Nat.digitChar_eq_seven (n := 7)).2 rfl]
    rw [hdig 8 (by decide), (Nat.digitChar_eq_eight (n := 8)).2 rfl]
    rw [hdig 9 (by decide), (Nat.digitChar_eq_nine (n := 9)).2 rfl]
    decide
  unfold List.Nodup at Hd ⊢
  rw [List.pairwise_map] at Hd ⊢
  refine Hd.imp ?_
  intro a b hab heq
  unfold kdFileName at heq
  exact hab (List.append_cancel_left heq)

section alloc
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [KdStor GF]

/-- The storage registry's invariant, with no storage registered yet. -/
theorem kdStorInv_alloc (E : CoPset) :
    ⊢ ghostMapAuth (KdStor.kdStorName (GF := GF)) 1 (∅ : GMap Loc KdStorRecT) ={E}=∗
      kdStorInv (GF := GF) := by
  iintro Ha
  unfold kdStorInv
  iapply inv_alloc
  inext
  unfold kdStorInvBody
  iexists ∅
  iframe Ha
  iapply BigSepM.bigSepM_empty.2
  itrivial

end alloc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem Main.wp_proof
    (wp_RandomConfig : RandomConfig.spec (GF := GF) (hG := hG))
    (wp_CounterClock : lintest.CounterClock.spec (GF := GF) (hG := hG))
    (wp_Run : ∀ [KdStor GF], Run.spec (GF := GF) (hG := hG))
    (wp_Stop : ∀ [KdStor GF], Cluster.Stop.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro dir fs Hrb Hfs
  wp_start as ⟨#Hcc, Hown⟩
  -- the storage registry
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := KdStorRecT) with ⟨%γreg, Hreg⟩
  letI : KdStor GF := ⟨γreg⟩
  imod kdStorInv_alloc (GF := GF) ⊤ $$ Hreg with #HstorInv
  -- the files: every replica's in `dir` claimed, absent
  imod durableFiles_alloc (GF := GF) kdFilesN ⊤ fs (kvreconf.allIds.map (kdFileName dir))
    (kdFileNames_nodup dir) $$ Hown with ⟨%γf, #Hfiles, Hfs'⟩
  rw [BigSepL.bigSepL_map]
  ihave Hfs' := (BigSepL.bigSepL_mono (Φ := fun _ i => dfile (GF := GF) γf (kdFileName dir i)
      (fs !! kdFileName dir i)) (Ψ := fun _ i => dfile (GF := GF) γf (kdFileName dir i) none)
      (fun {_ i} hk => by rw [Hfs i (List.mem_of_getElem? hk)])) $$ Hfs'
  try wp_auto
  wp_apply wp_RandomConfig as %cfg %Hcfg
  obtain ⟨Hopts, Hcl, Hops, Hp1, Hp3⟩ := Hcfg
  ihave #Hlpkg : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest
    $$ []
  · iPkgInit
  wp_apply wp_CounterClock kdClockN Hrb as %f ⟨%clockVal, #Hclk, Ht0⟩
  wp_apply wp_Run cfg clockVal (W64 0) ↑kdClockN f dir γf Hopts (by omega) lintestN_kdClockN
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

end kvdurable
end EtcdGrove
end Perennial
