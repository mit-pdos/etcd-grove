/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `State__Ready`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__Ready
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__persistState
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State__pendingFrom
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__Plus
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag__Minus

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

/-- A filtered bag's counts sum to at most the bag's. -/
theorem Bag.filter_sum_le (b : Bag) (q : Msg → Bool) :
    ((b.filterMsgs q).map Prod.snd).sum ≤ (b.map Prod.snd).sum := by
  unfold Bag.filterMsgs
  induction b with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons]
    split <;> simp <;> omega

theorem State.Ready.wp_proof (wp_clone : State.clone.spec (GF := GF) (hG := hG))
    (wp_persistState : State.persistState.spec (GF := GF) (hG := hG))
    (wp_pendingFrom : State.pendingFrom.spec (GF := GF) (hG := hG))
    (wp_Plus : Bag.Plus.spec (GF := GF) (hG := hG))
    (wp_Minus : Bag.Minus.spec (GF := GF) (hG := hG)) :
    State.Ready.spec (GF := GF) (hG := hG) := by
  intro p st i
  wp_start as ⟨#Hst, %Hi, %Hnd, %Hsum⟩
  ihave #Hst0 := Hst
  iunfold stateRO at Hst0
  icases Hst0 with ⟨%g, %sm, #Hp, #Hsrv, #Hm, %Hkeys, %Hnd0, #Hsrvs, #Hb1, #Hb2, %Hrc⟩
  icases typedPointsto_split _ _ _ $$ Hp with Hpf
  simp only [TypedPointsto.typedPointstoDef]
  icases Hpf with ⟨#P1, #P2, #P3, #P4, #P5, #P6, #P7, -⟩
  iapply wp_fupd
  wp_auto
  wp_apply wp_clone p st $$ [Hst] as %t Ht
  · iexact Hst
  try wp_auto
  wp_apply wp_persistState t st [] i $$ [Ht] as Ht
  · iframe Ht; ipureintro; exact Hi
  try wp_auto
  wp_apply wp_pendingFrom p st i $$ [Hst] as %gb #Hgb
  · iexact Hst
  try wp_auto
  have hnd2 : ((st.pendingFrom (uint.nat i)).map Prod.fst).Nodup := by
    unfold State.pendingFrom Bag.filterMsgs
    exact (List.filter_sublist).map Prod.fst |>.nodup Hnd
  have hsum2 : ((((st.pendingFrom (uint.nat i)).map Prod.snd).sum + (st.messages.map Prod.snd).sum : Nat) : Int) < 2 ^ 63 := by
    have := Bag.filter_sum_le st.pendingMessages (fun m => m.source == uint.nat i)
    unfold State.pendingFrom; omega
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.TypeAssumptions.ptr_Plus_unfold.method_unfold]
  wp_auto
  wp_apply wp_Plus _ _ _ _ $$ [Hgb Hb1] as %gp #Hgp
  · iframe Hgb Hb1; ipureintro; exact ⟨hnd2, hsum2⟩
  iunfold stateOwn at Ht
  icases Ht with ⟨%gt, %smt, Htp, #Htsrv, HtS, %Htkeys, %Htnd, Htsrvs, #Htb1, #Htb2, %Htrc⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Htp with ⟨Htp, %Htnn⟩
  icases typedPointsto_split _ _ _ $$ Htp with Htpf
  simp only [TypedPointsto.typedPointstoDef]
  icases Htpf with ⟨T1, T2, T3, T4, T5, T6, T7, -⟩
  try wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.TypeAssumptions.ptr_Minus_unfold.method_unfold]
  wp_auto
  wp_apply wp_Minus _ _ _ _ $$ [Hb2 Hgb] as %gm #Hgm
  · iframe Hb2 Hgb; ipureintro; exact Hnd
  try wp_auto
  ihave Htp : t ↦ ({ gt with Messages' := gp, PendingMessages' := gm } : G.State) $$ [T1 T2 T3 T4 T5 T6 T7]
  · iapply typedPointsto_combine _ _ _ Htnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  ihave Ht : stateOwn (GF := GF) t (st.ready (uint.nat i)) [uint.nat i] $$ [Htp HtS Htsrvs]
  · iunfold stateOwn
    iexists _, smt
    iframe Htp HtS
    unfold State.ready State.persistState State.upd
    simp only
    iframe Htsrv Htsrvs Hgp Hgm
    ipureintro; exact ⟨Htkeys, Htnd, Htrc⟩
  imod stateOwn_persist $$ Ht with #Ht
  imodintro
  iapply HΦ
  iexact Ht

end proof

end Etcdraft
end EtcdGrove
end Perennial
