/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Replica__applyOp.lean`. Lean-first (no
Rocq counterpart).

The datum decoded; if it is an operation, under the lock its applied-table entry decides: applied
before, its recorded answer; else the store's map moves by it (a `Put` sets its key) and the table
records the key's value after it, written with both halves of the table (the applier's and the
lock's, `Halves.lean`). The waiter of the operation, if any, is removed and answered after the
unlock with `waitP`: the answer is the datum's in the history of `ap` or of `ap ++ [e]`, both
committed.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica__applyOp
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.decode
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.PureLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Halves
public import Proof.go_etcd_io.raft.v3.FrameH

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [StorageModel GF] [AllG GF]

/-- The configuration's facts carry past a normal entry. -/
theorem cfg_normal (RA : RaftAssume (GF := GF)) (γr : RNames) (n : Loc) (ap : List LogEntry)
    (e : LogEntry) (csp : Loc) (c : ConfStateM) (m : Membership) (ht : e.type = W32 0) :
    isCommittedLogLb γr.cluster (ap ++ [e]) ∗
      ((⌜confStateIs c m⌝ ∗ confAt γr.cluster ap.length m) ∨
        (⌜csp = null ∧ m = Membership.empty⌝ ∗ RA.nodeStopped n γr.cluster kvrRaftN)) ⊢
      ((⌜confStateIs c m⌝ ∗ confAt γr.cluster (ap ++ [e]).length m) ∨
        (⌜csp = null ∧ m = Membership.empty⌝ ∗ RA.nodeStopped n γr.cluster kvrRaftN)) := by
  iintro ⟨#Hce, Hc⟩
  icases Hc with (⟨%Hcs, #Hca⟩ | Hs)
  · ileft
    isplitr
    · ipureintro; exact Hcs
    rw [List.length_append, List.length_singleton]
    iapply kvr_confAt_normal γr.cluster (ap ++ [e]) ap.length e m (by simp)
      (by unfold LogEntry.isConfChange; rw [ht]; intro h; rcases h with h | h <;> word)
    iframe Hce Hca
  · iright; iexact Hs

set_option hygiene false in
/-- `applyOp` from the waiters' lookup on: the waiter of the operation, if any, removed; the
unlock, with the lock's half `HA2` of the table `A'` and its committed prefix `apS` (`HapS`,
`HAS`); the answer `v` sent with `Hw`; the end state from `Hfin`. -/
local macro "applyop_tail" : tactic => `(tactic| (
    wp_apply wp_map_lookup2 go.string (go.GoType.ChannelType go.ChanDir.sendrecv go.string) mW W
      e.data (DFrac.own 1) $$ [$(frameH `HW)] as HW
    cases HWs : W !! e.data with
    | none =>
      simp only [Option.getD_none, Option.isSome_none, decide_false]
      try wp_auto
      wp_apply sync.Mutex.wp_Unlock _ _ $$ [$(frameH `Hmu) $(frameH `Hlocked) HmA' HA2 Hcs' Hidx'
          HmW HW Hwaiters Hns Hseq HmR HRd Hreads]
      · inext
        unfold lockInv repShared
        iexists ns, mW, W, mR, Rd
        iframe
        isplitl [HmA' HA2 Hcs' Hidx']
        · iexists mA, A', csp', c', idx', apS
          iframe HmA' HA2 Hcs' Hidx' HcsO' HapS
          ipureintro; exact HAS
        · ipureintro; exact HRdom
      try wp_auto
      iapply HΦ
      iapply Hfin $$ %K' %A' %HKA HmK HK HmA HA1 Hcs Hidx
    | some ch =>
      simp only [Option.getD_some, Option.isSome_some, _root_.decide_true]
      try wp_auto
      wp_apply wp_mapDelete mW W e.data go.string
        (go.GoType.ChannelType go.ChanDir.sendrecv go.string) $$ [$(frameH `HW)] as HW
      icases (BigSepM.bigSepM_delete (Φ := fun d ch => waiterOk (GF := GF) γr d ch) HWs).1
        $$ Hwaiters with ⟨Hwt, Hwaiters⟩
      iunfold waiterOk at Hwt
      icases Hwt with ⟨%γh, #Hho, Hprod⟩
      try wp_auto
      wp_apply sync.Mutex.wp_Unlock _ _ $$ [$(frameH `Hmu) $(frameH `Hlocked) HmA' HA2 Hcs' Hidx'
          HmW HW Hwaiters Hns Hseq HmR HRd Hreads]
      · inext
        unfold lockInv repShared
        iexists ns, mW, GMap.delete e.data W, mR, Rd
        iframe
        isplitl [HmA' HA2 Hcs' Hidx']
        · iexists mA, A', csp', c', idx', apS
          iframe HmA' HA2 Hcs' Hidx' HcsO' HapS
          ipureintro; exact HAS
        · ipureintro; exact HRdom
      try wp_auto
      wp_apply wp_handoff_send (t := go.string) γh ch (waitP γr e.data) iprop(True) iprop(False)
        v $$ [$(frameH `Hho) $(frameH `Hprod) $(frameH `Hw)]
      iintro -
      try wp_auto
      iapply HΦ
      iapply Hfin $$ %K' %A' %HKA HmK HK HmA HA1 Hcs Hidx
  ))

theorem Replica.applyOp.wp_proof (wp_decode : decode.spec (GF := GF) (hG := hG)) :
    Replica.applyOp.spec (GF := GF) (hG := hG) := by
  intro RA γr id n r ap idx csp m mA A e dsl Hty Hlen'
  wp_start as ⟨#Hmu, Hown, #Hd, #Hce⟩
  iunfold repOwn at Hown
  iNamed Hown
  ihave #Hcfg' := cfg_normal RA γr n ap e csp c m Hty $$ [$Hce $Hcfg]
  -- the end state, from new map and table facts
  ihave Hfin : iprop(∀ (K' A' : GMap (List w8) (List w8)),
      ⌜(∀ k, (K' !! k).getD [] = kvFold (logHist (ap ++ [e])) k) ∧
        AppliedOk A' (logHist (ap ++ [e]))⌝ -∗
      r.[RReplica, go!"kv"] ↦ mK -∗ mK ↦$ K' -∗
      r.[RReplica, go!"applied"] ↦{DFrac.own (1 : Qp).half} mA -∗
      mA ↦${DFrac.own (1 : Qp).half} A' -∗
      r.[RReplica, go!"cs"] ↦{DFrac.own (1 : Qp).half} csp -∗
      r.[RReplica, go!"index"] ↦{DFrac.own (1 : Qp).half} idx -∗
      ∃ A'', repOwn RA γr n r (ap ++ [e]) idx csp m mA A'') $$ [Hcfg']
  · iintro %K' %A' %HKA HmK HK HmA HA Hcs Hidx
    obtain ⟨HK', HA'⟩ := HKA
    iexists A'
    unfold repOwn
    iexists mK, K', c
    iframe HmK HK HmA HA Hcs Hidx Hce HcsO Hcfg'
    ipureintro
    refine ⟨by simp; omega, HK', HA'⟩
  wp_auto
  wp_apply wp_decode dsl e.data DFrac.discard $$ [$Hd] as -
  cases Hdec : decodeOp e.data with
  | none =>
    unfold decodeRet; rw [Hdec]
    wp_auto
    iapply HΦ
    have H := hist_skip ap e K A HA Hval (by
      by_cases hd : e.data = []
      · exact .inl (odOf_nil e hd)
      · exact .inr ⟨e.data, odOf_normal e Hty hd, .inl Hdec⟩)
    iapply Hfin $$ %K %A %H HmK HK HmA HA Hcs Hidx
  | some x =>
    obtain ⟨i, kd, key, val⟩ := x
    unfold decodeRet; rw [Hdec]
    have Hne := decodeOp_ne_nil e.data _ Hdec
    have Ho := odOf_normal e Hty Hne
    wp_auto
    wp_apply wp_bytes_to_string dsl e.data DFrac.discard $$ [$Hd] as -
    wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HR⟩
    iNamed HR
    iunfold repShared at Hrep
    icases Hrep with ⟨%mA', %A0, %csp', %c', %idx', %ap', HmA', HA', Hcs', Hidx', #HcsO', #Hap', %HA0⟩
    icombine HmA HmA' gives %HmAeq
    subst HmAeq
    icases ownMap_halves_combine mA A A0 $$ [$HA $HA'] with ⟨%HAeq, HAf⟩
    subst HAeq
    try wp_auto
    wp_apply wp_map_lookup2 go.string go.string mA A e.data (DFrac.own 1) $$ [$HAf] as HAf
    have Hdsome : (decodeOp e.data).isSome := by rw [Hdec]; rfl
    rw [appliedOk_lookup A _ e.data HA Hdsome]
    try wp_auto
    wp_if_destruct
    · -- applied before: its recorded answer
      have Hmem : e.data ∈ logHist ap := of_decide_eq_true Hif
      have HKA := hist_skip ap e K A HA Hval (.inr ⟨e.data, Ho, .inr Hmem⟩)
      obtain ⟨v, Hv⟩ : ∃ v, A !! e.data = some v := by
        have := (HA.1 e.data).2 ⟨Hmem, Hdsome⟩
        exact Option.isSome_iff_exists.mp this
      ihave #Hw : waitP γr e.data ((A !! e.data).getD (zero_val (List w8))) $$ []
      · unfold waitP
        iexists ap
        iframe Hap
        ipureintro; rw [Hv]; exact HA.2 _ _ Hv
      icases ownMap_halves_split mA A $$ [$HAf] with ⟨HA1, HA2⟩
      obtain ⟨K', HKe⟩ : ∃ K', K' = K := ⟨_, rfl⟩
      subst HKe
      obtain ⟨A', HAe⟩ : ∃ A', A' = A := ⟨_, rfl⟩
      subst HAe
      obtain ⟨apS, HapSe⟩ : ∃ x, x = ap' := ⟨_, rfl⟩
      subst HapSe
      ihave #HapS := Hap'
      have HAS := HA0
      generalize (A' !! e.data).getD (zero_val (List w8)) = v
      applyop_tail
    · -- the first occurrence: the store's map moves, the table records the answer
      have Hnm : e.data ∉ logHist ap := fun h => Hif (decide_eq_true h)
      obtain ⟨K', HK'⟩ : ∃ K', K' = if kd = opPutB then <[key := val]> K else K := ⟨_, rfl⟩
      wp_if_destruct
      wp_apply wp_mapInsert go.string mK K key val $$ [$HK] as HK
      rw [show <[key := val]> K = K' by rw [HK', if_pos (show W8 1 = opPutB from rfl)]]
      rotate_left
      rw [show K = K' by rw [HK', if_neg (show ¬ kd = opPutB from Hif)]]
      rotate_left
      all_goals
        wp_apply wp_map_lookup1 go.string go.string mK K' key (DFrac.own 1) $$ [$HK] as HK
        try wp_auto
        wp_apply wp_mapInsert go.string mA A e.data ((K' !! key).getD (zero_val (List w8)))
          $$ [$HAf] as HAf
        try wp_auto
        have HKA0 := hist_insert ap e K A e.data i _ key val HA Hval Ho Hnm Hdec K' HK'
        rw [show (zero_val (List w8)) = ([] : List w8) from rfl]
        obtain ⟨A', HAe⟩ : ∃ A', A' = A.insert e.data ((K' !! key).getD []) := ⟨_, rfl⟩
        rw [← HAe] at HKA0 ⊢
        have HKA := HKA0
        icases ownMap_halves_split mA A' $$ [$HAf] with ⟨HA1, HA2⟩
        ihave #Hw : waitP γr e.data ((K' !! key).getD []) $$ []
        · unfold waitP
          iexists ap ++ [e]
          iframe Hce
          ipureintro
          exact HKA0.2.2 _ _ (by rw [HAe]; show (A.insert e.data _ !! e.data) = _; rw [GMap.lookup_insert_eq])
        obtain ⟨apS, HapSe⟩ : ∃ x, x = ap ++ [e] := ⟨_, rfl⟩
        rw [← HapSe] at HKA0
        ihave #HapS : isCommittedLogLb γr.cluster apS $$ []
        · rw [HapSe]; iexact Hce
        have HAS := HKA0.2
        generalize (K' !! key).getD [] = v
        applyop_tail

end proof

end kvreconf
end EtcdGrove
end Perennial
