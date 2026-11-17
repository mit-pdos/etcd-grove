-- The copy for the part `RaftNoAx/` of `Proof/github_com/mit_pdos/etcd_grove/examples/raft/kvdurable/Main.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurable/Main.lean`. Lean-first (no Rocq
counterpart). kvreconf's, with the files.

The storage registry (`KdStor`, `kdStorInv`) and the files' invariant (`durableFiles_alloc`, from
the program's files, claiming every replica id's file in `dir`, absent) are allocated; then
`RandomConfig`, the counter clock, `Run` (which allocates the store's ghost state and gives the
crasher's token back) and `Stop` (which takes it).
-/
module

public import RaftNoAx.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvdurable.Main
public import RaftNoAx.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvdurable.Run
public import RaftNoAx.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvdurable.RandomConfig
public import RaftNoAx.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvdurable.Cluster__Stop
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.lintest.CounterClock

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The namespace of `Main`'s clock's invariant. -/
abbrev kdClockN : Namespace := nroot.@"kvdurable_clock"

theorem lintestN_kdClockN : (↑lintest.lintestN : CoPset) ⊆ ⊤ \ ↑kdClockN :=
  mask_ndot_ne' nroot "lintest" "kvdurable_clock" (by decide)

/-- Two lists of decimal digits with the same bytes are equal. -/
private theorem digits_map_inj {l1 l2 : List Char} (f : Char → w8)
    (hf : ∀ c d, c.isDigit → d.isDigit → f c = f d → c = d)
    (h1 : ∀ c ∈ l1, c.isDigit) (h2 : ∀ c ∈ l2, c.isDigit) (h : l1.map f = l2.map f) : l1 = l2 := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp_all
  | cons a t IH =>
    cases l2 with
    | nil => simp at h
    | cons b u =>
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.mem_cons, forall_eq_or_imp] at h1 h2
      rw [hf a b h1.1 h2.1 h.1, IH h1.2 h2.2 h.2]

/-- `itoa`'s decimal names are distinct (2026-11-16, kvraftN: until then nine one-digit names,
checked by `decide`). -/
theorem decimalB_inj (m n : Nat) (h : decimalB m = decimalB n) : m = n := by
  unfold decimalB at h
  have hf : ∀ c d : Char, c.isDigit → d.isDigit →
      W8 (c.toNat : Int) = W8 (d.toNat : Int) → c = d := by
    intro c d hc hd he
    simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at hc hd
    have hc' : c.toNat ≤ 57 := hc.2
    have hd' : d.toNat ≤ 57 := hd.2
    have := congrArg (fun w : w8 => uint.nat w) he
    apply Char.toNat_inj.mp; word
  have hl : Nat.toDigits 10 m = Nat.toDigits 10 n :=
    digits_map_inj _ hf (fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc)
      (fun c hc => Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc) h
  rw [← Nat.ofDigitChars_ten_toDigits (n := m), hl, Nat.ofDigitChars_ten_toDigits]

/-- The files of the replicas `1 … m` in `dir` are distinct names. -/
theorem kdFileNamesM_nodup (dir : GoString) (m : Nat) (hm : m < 2 ^ 62) :
    ((raft_kvreconf.bootVoters m).map (kdFileName dir)).Nodup := by
  have Hd := raft_kvreconf.bootVoters_nodup m hm
  unfold List.Nodup at Hd ⊢
  rw [List.pairwise_map]
  refine Hd.imp ?_
  intro a b hab heq
  apply hab
  unfold kdFileName at heq
  have := decimalB_inj _ _ (List.append_cancel_left heq)
  word

/-- The replicas' files in `dir` are distinct names (`Main`'s nine). -/
theorem kdFileNames_nodup (dir : GoString) :
    (raft_kvreconf.allIds.map (kdFileName dir)).Nodup :=
  kdFileNamesM_nodup dir 9 (by omega)

section alloc
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvdurable.Assumptions]
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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvdurable.Assumptions]
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
  imod durableFiles_alloc (GF := GF) kdFilesN ⊤ fs (raft_kvreconf.allIds.map (kdFileName dir))
    (kdFileNames_nodup dir) $$ Hown with ⟨%γf, #Hfiles, Hfs'⟩
  rw [BigSepL.bigSepL_map]
  ihave Hfs' := (BigSepL.bigSepL_mono (Φ := fun _ i => dfile (GF := GF) γf (kdFileName dir i)
      (fs !! kdFileName dir i)) (Ψ := fun _ i => dfile (GF := GF) γf (kdFileName dir i) none)
      (fun {_ i} hk => by rw [Hfs i (List.mem_of_getElem? hk)])) $$ Hfs'
  try wp_auto
  wp_apply wp_RandomConfig as %cfg %Hcfg
  obtain ⟨Hopts, Hmax, Hcl, Hops, Hp1, Hp3⟩ := Hcfg
  ihave Hfs' : iprop([∗list] i ∈ raft_kvreconf.bootVoters (uint.nat cfg.Options'.MaxReplicas'),
      dfile (GF := GF) γf (kdFileName dir i) none) $$ [Hfs']
  · rw [Hmax, show uint.nat (W64 9) = 9 from rfl]; iexact Hfs'
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
