/-
Proof of `KvRaft/Spec/.../kvcheck/Check.lean` (kvdurable's `Run`/`Main` over the network). The
addresses split and validated (`ValidAddrs`: if it fails, `Check` returns at once; if it holds, the
store's resources); the checker built (its
mutex guarding the counters at `0`, the store's counter predicates `kvCnt`, `lastConf` nil); the
proposers and the disruptor run in goroutines joined by a wait group (`sync.join`, an empty
resource); the clients run `lintest.Run`'s test over a driver's copy of the store's state
(`kvAu_of_run`, `DriverLemmas.lean`), each operation one of `do`/`read`, logically atomic over the
store; with no timeout porcupine answers `Ok`. Once the clients are done the stop channel is closed
and the group waited on.
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Check
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker__do
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker__read
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker__reconfigure
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker__disrupt
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.below
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.SplitAddrs
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.ValidAddrs
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Model
public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Gen
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.lintest.Run
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.lintest.CounterClock
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.DriverLemmas
public import Perennial.Spec.sync.WaitGroup__Add
public import Perennial.Spec.sync.WaitGroup__Done
public import Perennial.Spec.sync.WaitGroup__Wait
public import Perennial.Proof.sync.WaitGroupJoin
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net kvraft go_etcd_io.raft.v3
open github_com.anishathalye.porcupine
open raft_kvreconf (KVMap kvUpd opPutB opGetB)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Assumptions]
variable [field_sem : net.FieldAssumptions] [go.IntoValInj GoString]
variable [kvraft_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

theorem Check.wp_proof
    (wp_SplitAddrs : SplitAddrs.spec (GF := GF) (hG := hG))
    (wp_ValidAddrs : ValidAddrs.spec (GF := GF) (hG := hG))
    (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_reconfigure : checker.reconfigure.spec (GF := GF) (hG := hG))
    (wp_disrupt : checker.disrupt.spec (GF := GF) (hG := hG))
    (wp_do : checker.do.spec (GF := GF) (hG := hG))
    (wp_read : checker.read.spec (GF := GF) (hG := hG))
    (wp_Model : Model.spec (GF := GF) (hG := hG))
    (wp_Gen : Gen.spec (GF := GF) (hG := hG))
    (wp_CounterClock : lintest.CounterClock.spec (GF := GF) (hG := hG))
    (wp_lintestRun : lintest.Run.spec (GF := GF) (hG := hG)) :
    Check.spec (GF := GF) (hG := hG) := by
  intro γ addrs voters Hrb
  wp_start as ⟨#Hcc, #Hglob, Hres⟩
  ihave #Hkpkg : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft
    $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_SplitAddrs addrs $$ [$Hkpkg] as %sl ⟨Hsl, Hcap⟩
  try wp_auto
  wp_apply wp_ValidAddrs sl (DFrac.own 1) (splitAddrs addrs) voters $$ [$Hkpkg $Hsl] as Hsl
  -- invalid addresses: `Check` returns at once
  by_cases Hvalid : validAddrs (splitAddrs addrs) (uint.nat voters) = true
  case neg =>
    rw [Bool.not_eq_true] at Hvalid
    rw [Hvalid]
    try wp_auto
    iapply HΦ
    itrivial
  ihave ⟨#Hinv, Hval, Hopn, Hrseq, #Hprot⟩ := Hres $$ %Hvalid
  rw [Hvalid]
  have Hv := Hvalid
  simp only [validAddrs, decide_eq_true_eq] at Hv
  obtain ⟨Hok, Hnd, Hlen32, Hv1, Hv2⟩ := Hv
  try wp_auto
  -- the checker: `addrs` read-only, the mutex guarding the counters at `0` with the store's
  -- counter predicates
  icases typedPointsto_split _ _ _ $$ «$r0» with Hc0
  simp only [TypedPointsto.typedPointstoDef]
  icases Hc0 with ⟨Haddrs, Hmu, HnOp, HnRd, HlC, -⟩
  ipersist Haddrs
  imod ownSlice_persist sl _ _ $$ Hsl with #Hsl
  imod sync.init_Mutex (checkerInv «$r0_ptr» (kvCnt γ (splitAddrs addrs).length)) ⊤ _
    $$ Hmu [HnOp HnRd HlC Hopn Hrseq] with #Hmu
  · inext
    unfold checkerInv
    rw [show (W64 0 : w64) = (0 : w64) from rfl]
    iexists 0, 0, null, ConfStateM.mk [] [] [] [] false
    iframe HnOp HnRd HlC Hopn Hrseq
    unfold csOpt
    ileft
    ipureintro; exact ⟨rfl, rfl⟩
  ihave #Hck : isCheckerP (kvFacts γ (fun _ => True)) «$r0_ptr» (kvCnt γ (splitAddrs addrs).length)
      (splitAddrs addrs) $$ []
  · unfold isCheckerP isChecker
    iframe Hprot Hglob
    isplitl
    · iexists sl
      iframe Haddrs Hsl Hmu
    ipureintro; omega
  ipersist c
  try wp_auto
  -- the `stop` broadcast
  wp_apply chan.wp_make1 (V := Unit) as %sc %γsc ⟨#Hsc, %_, Hsoc⟩
  imod alloc_broadcast_chan (E := ⊤) (iprop(True) : IProp GF) γsc sc $$ Hsc Hsoc with Hpend
  icases ownBroadcastChan_open _ _ _ _ $$ Hpend with ⟨%γbi, #Hbi, Hpend⟩
  ihave #Hunk := ownBroadcastChan_close sc γsc iprop(True) Broadcast.Unknown γbi $$ [$Hbi]
  ihave Hpend := ownBroadcastChan_close sc γsc iprop(True) Broadcast.Pending γbi $$ [$Hbi $Hpend]
  try wp_auto
  -- the wait group
  imod sync.init_WaitGroup (sync.join.wgjN.@"wg") wg_ptr $$ wg with ⟨%γwg, Hwg⟩
  imod sync.join.init wg_ptr γwg $$ Hwg with Hwg
  ipersist stop
  wp_apply wp_below (W64 3) $$ [$Hpkg] as %np %Hnp
  have Hnp3 : uint.Z np < 3 := Hnp.2 (by decide)
  try wp_auto
  -- the proposers
  ihave HI : (∃ (k : w64) (na : w32),
      "i" ∷ i_ptr ↦ k ∗ "Hwg" ∷ sync.join.ownAdder wg_ptr na iprop(True) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ 3 ∧ sint.Z na = sint.Z k⌝ : IProp GF) $$ [i Hwg]
  · iexists W64 0, W32 0
    iframe
    ipureintro
    exact ⟨by decide, by decide, by decide⟩
  wp_for HI
  try wp_auto
  wp_if_destruct
  · have Hlt : sint.Z k < 3 := by word
    wp_apply (sync.join.WaitGroup.wp_Add_of sync.WaitGroup.wp_Add iprop(True) wg_ptr _ na)
      $$ [Hwg] as ⟨Hwg, Hdone⟩
    · iframe; ipureintro; word
    try wp_auto
    wp_apply wp_fork $$ [Hdone]
    · try wp_auto
      wp_apply wp_reconfigure (kvFacts γ (fun _ => True)) «$r0_ptr» _ (splitAddrs addrs) sc γsc
        (fun _ => trivial) $$ [$Hpkg $Hck $Hunk]
      try wp_auto
      wp_apply (sync.join.WaitGroup.wp_Done_of sync.WaitGroup.wp_Done iprop(True) wg_ptr)
        $$ [$Hdone]
      itrivial
    wp_for_post
    iframe
    iexists (k + W64 1), (na + W32 1)
    iframe
    unfold named
    isplitl [Hwg]
    · iapply sync.join.ownAdder_wand $$ [] Hwg
      iintro _
      itrivial
    ipureintro
    refine ⟨by word, by word, by word⟩
  -- the disruptions
  wp_apply (sync.join.WaitGroup.wp_Add_of sync.WaitGroup.wp_Add iprop(True) wg_ptr _ na)
    $$ [Hwg] as ⟨Hwg, Hdone⟩
  · iframe; ipureintro; word
  try wp_auto
  wp_apply wp_fork $$ [Hdone]
  · try wp_auto
    wp_apply wp_disrupt (kvFacts γ (fun _ => True)) «$r0_ptr» _ (splitAddrs addrs) sc γsc
      $$ [$Hpkg $Hck $Hunk]
    try wp_auto
    wp_apply (sync.join.WaitGroup.wp_Done_of sync.WaitGroup.wp_Done iprop(True) wg_ptr)
      $$ [$Hdone]
    itrivial
  -- the driver's copy of the store's state, and the invariant tying it to the client's half
  try wp_auto
  ipersist apply
  iunfold rkvVal at Hval
  icases Hval with ⟨%Hs0, Hv, %HH0⟩
  imod ghostVar_alloc (GF := GF) Hs0 with ⟨%γc, Hc⟩
  icases (ghostVar_split_half γc 1 Hs0).1 $$ Hc with ⟨Hc1, Hc2⟩
  let γd : KdNames := { γ with r := { γ.r with val := γc } }
  imod inv_alloc checkN ⊤ iprop(∃ x, rkvVal γ x ∗ rkvVal γd x) $$ [Hv Hc1] with #HinvC
  · inext
    iexists raft_kvreconf.kvEmpty
    unfold rkvVal
    isplitl [Hv]
    · iexists Hs0; iframe; ipureintro; exact HH0
    · iexists Hs0; iframe; ipureintro; exact HH0
  wp_apply wp_Model $$ [$Hkpkg] as %m #Hm
  ihave #Hlpkg : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.lintest
    $$ []
  · iPkgInit
  try wp_auto
  wp_apply wp_CounterClock clockN (by omega) $$ [$Hlpkg] as %clk ⟨%clockVal, #Hclk, Ht0⟩
  try wp_auto
  wp_apply wp_lintestRun KVMap kvS m _ _ clk kvInOk (rkvVal γd) clockVal (W64 0) checkMask ↑clockN
    (W64 4) (W64 100) (W64 0) lintestN_checkMask lintestN_clockN (by decide) (by decide) (by decide)
    (by decide) $$ [Hc2 Ht0]
  · isplitr
    · iexact Hcc
    isplitr
    · iexact Hm
    isplitr
    · -- `apply`
      unfold lintest.applySpec
      iintro %i
      iintro !> %Φ' ⟨%Hin, Htt⟩ HAU
      obtain ⟨x, rfl, Hk, Hv⟩ := Hin
      wp_auto
      wp_if_destruct
      · -- Put
        replace Hif : x.Kind' = opPutB := Hif
        ihave HAU' := kvAu_of_run γ γd x (raft_kvreconf.kvNext (W8 1) x.Key' x.Val') (fun _ => [])
          (fun o => iprop(∀ o',
            ⌜∀ s, kvS (GF := GF).M.step s (boxIn x, o') = kvS (GF := GF).M.step s (boxIn x, o)⌝ ∗
            kvS.ioOk (GF := GF) (boxIn x) o' ∗ @threadTok GF GooseGlobalGS.gooseAllG _ -∗ Φ' #o'))
          (fun s => by
            unfold inStep raft_kvreconf.kvNext
            rw [ite_eq_left Hif, ite_eq_left (by unfold raft_kvreconf.opPutB; rfl)])
          (fun s => by unfold inOut; rw [ite_eq_left Hif]) $$ HinvC HAU
        wp_apply wp_do γ (fun _ => True) «$r0_ptr» (splitAddrs addrs) (W8 1) x.Key' x.Val'
          (fun _ => iprop(∀ o',
            ⌜∀ s, kvS (GF := GF).M.step s (boxIn x, o') = kvS (GF := GF).M.step s (boxIn x, boxS [])⌝ ∗
            kvS.ioOk (GF := GF) (boxIn x) o' ∗ @threadTok GF GooseGlobalGS.gooseAllG _ -∗ Φ' #o'))
          Hk Hv $$ [$Hpkg $Hck $Hinv $HAU'] as %v HΨ
        try wp_auto
        iapply HΨ
        iframe Htt
        ipureintro; exact ⟨fun _ => rfl, ⟨x, rfl⟩, [], rfl⟩
      replace Hnp : ¬ x.Kind' = opPutB := Hif
      wp_if_destruct
      · -- Get
        replace Hif : x.Kind' = opGetB := Hif
        have H21 : ¬ (W8 2 = raft_kvreconf.opPutB) := by unfold raft_kvreconf.opPutB; decide
        ihave HAU' := kvAu_of_run γ γd x (raft_kvreconf.kvNext (W8 2) x.Key' [])
          (fun s => raft_kvreconf.kvNext (W8 2) x.Key' [] s x.Key')
          _
          (fun s => by unfold inStep raft_kvreconf.kvNext; rw [ite_eq_right Hnp, ite_eq_right H21])
          (fun s => by unfold inOut raft_kvreconf.kvNext; rw [ite_eq_right Hnp, ite_eq_right H21])
          $$ HinvC HAU
        wp_apply wp_do γ (fun _ => True) «$r0_ptr» (splitAddrs addrs) (W8 2) x.Key' []
          (fun v => iprop(∀ o',
            ⌜∀ s, kvS (GF := GF).M.step s (boxIn x, o') = kvS (GF := GF).M.step s (boxIn x, boxS v)⌝ ∗
            kvS.ioOk (GF := GF) (boxIn x) o' ∗ @threadTok GF GooseGlobalGS.gooseAllG _ -∗ Φ' #o'))
          Hk (by simp) $$ [$Hpkg $Hck $Hinv $HAU'] as %v HΨ
        try wp_auto
        iapply HΨ
        iframe Htt
        ipureintro; exact ⟨fun _ => rfl, ⟨x, rfl⟩, v, rfl⟩
      · -- Read
        replace Hng : ¬ x.Kind' = opGetB := Hif
        ihave HAU' := kvAu_of_run γ γd x (fun s => s) (fun s => s x.Key')
          _
          (fun s => by unfold inStep; rw [ite_eq_right Hnp])
          (fun s => by unfold inOut; rw [ite_eq_right Hnp]) $$ HinvC HAU
        wp_apply wp_read γ (fun _ => True) «$r0_ptr» (splitAddrs addrs) x.Key'
          (fun v => iprop(∀ o',
            ⌜∀ s, kvS (GF := GF).M.step s (boxIn x, o') = kvS (GF := GF).M.step s (boxIn x, boxS v)⌝ ∗
            kvS.ioOk (GF := GF) (boxIn x) o' ∗ @threadTok GF GooseGlobalGS.gooseAllG _ -∗ Φ' #o'))
          Hk $$ [$Hpkg $Hck $Hinv $HAU'] as %v HΨ
        try wp_auto
        iapply HΨ
        iframe Htt
        ipureintro; exact ⟨fun _ => rfl, ⟨x, rfl⟩, v, rfl⟩
    isplitr
    · -- `gen`
      unfold lintest.genSpec
      iintro %id
      iintro !> %Φ' _ HΦ'
      wp_apply wp_Gen $$ [$Hkpkg] as %i #Hi
      iapply HΦ' $$ Hi
    isplitr
    · iexact Hclk
    iframe
    unfold rkvVal
    iexists Hs0
    iframe
    ipureintro
    exact HH0
  iintro %r %Hr
  have Hok : r = go!"Ok" := Hr.2 (by decide)
  subst Hok
  try wp_auto
  wp_apply wp_broadcast_chan_close sc γsc iprop(True) $$ [$Hpend] as -
  · iintro !>; itrivial
  try wp_auto
  wp_apply (sync.join.WaitGroup.wp_Wait_of sync.WaitGroup.wp_Wait _ _ wg_ptr) $$ [$Hwg] as -
  try wp_auto
  iapply HΦ
  itrivial

end proof

end raft_kvcheck
end EtcdGrove
end Perennial
