/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Run.lean`. Lean-first (no Rocq
counterpart). kvreconf's, with the allocation `StartCluster` takes (`kd_alloc`) and the crashes.

`kd_alloc` allocates the store's ghost state over raft's cluster (the files' entries are the
caller's), `StartCluster` starts the voters. The proposers, the disruptions and the crashes run in
goroutines joined by a wait group (`sync.join`): the crashes' goroutine takes the crasher's token and
gives it back through its `Done` (the group's resource is the token: when the crashes do not run, the
token goes into it at once). The clients run `lintest.Run`'s test over a driver's copy of the store's
state (`kdAu_of_run`). Once the clients are done the stop channel is closed and the group waited on:
the token is back.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Run
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.StartCluster
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__Put
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__Get
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__Read
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__Reconfigure
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__Disrupt
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Model
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Gen
public import Spec.github_com.mit_pdos.etcd_grove.examples.lintest.Run
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.DriverLemmas
public import Perennial.Spec.sync.WaitGroup__Add
public import Perennial.Spec.sync.WaitGroup__Done
public import Perennial.Spec.sync.WaitGroup__Wait
public import Perennial.Proof.sync.WaitGroupJoin
public import Perennial.Proof.sync.Link
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster__Crash
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Alloc
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.DefsLaws

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.raft.v3
open github_com.anishathalye.porcupine
open kvreconf (KVMap kvUpd opPutB opGetB)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- The crasher's token is timeless (it comes back through the wait group under a later). -/
instance crasher_timeless (γ : KdNames) : Timeless (crasher (GF := GF) γ) := by
  unfold crasher; infer_instance

theorem Run.wp_proof
    (wp_StartCluster : StartCluster.spec (GF := GF) (hG := hG))
    (wp_Reconfigure : Cluster.Reconfigure.spec (GF := GF) (hG := hG))
    (wp_Disrupt : Cluster.Disrupt.spec (GF := GF) (hG := hG))
    (wp_Crash : Cluster.Crash.spec (GF := GF) (hG := hG))
    (wp_Put : Cluster.Put.spec (GF := GF) (hG := hG))
    (wp_Get : Cluster.Get.spec (GF := GF) (hG := hG))
    (wp_Read : Cluster.Read.spec (GF := GF) (hG := hG))
    (wp_Model : Model.spec (GF := GF) (hG := hG))
    (wp_Gen : Gen.spec (GF := GF) (hG := hG))
    (wp_lintestRun : lintest.Run.spec (GF := GF) (hG := hG)) :
    Run.spec (GF := GF) (hG := hG) := by
  intro cfg clockVal t0 Eclk clock dir γf Hopts Hrb HN Hc0 Hc31 Hops Hmul Hprop
  wp_start as ⟨#Hcc, #Hstor, #Hclk, Ht0, #Hfiles, Hfs⟩
  -- the store's ghost state, over raft's cluster
  imod kd_alloc cfg.Options' dir γf ⊤ (by omega) Hopts $$ Hfiles Hfs with
    ⟨%γr, %Hγ, #Hkc, Hvs, Hja, Hfresh, Hopn, Hnid, Hrseq, Hcur, Hcr, Hval⟩
  try wp_auto
  -- (2026-11-02, stage II (t)) `RestartNode`'s `readyFits`: no bootstrap log, the receipts' bound
  ihave #Hfits : readyFits (GF := GF) γr.r.cluster kdRaftN $$ []
  · iapply readyFits_intro (GF := GF) γr.r.cluster kdRaftN (by rw [Hγ.2.2]; omega)
  wp_apply wp_StartCluster γr cfg.Options' dir Hopts $$ [$Hkc $Hstor $Hfits $Hvs $Hja $Hfresh $Hopn $Hnid
      $Hrseq $Hcur] as %c #Hcl
  · iframe #
    ipureintro; exact ⟨Hγ.2.1, Hγ.2.2⟩
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
  ipersist c
  icases typedPointsto_split _ _ _ $$ cfg with cfg
  try simp only [TypedPointsto.typedPointstoDef]
  icases cfg with ⟨Options, Clients, Ops, Proposers, ReconfPause, DisruptPause, CrashPause, -⟩
  ipersist ReconfPause
  ipersist DisruptPause
  ipersist CrashPause
  ipersist stop
  -- the proposers
  ihave HI : (∃ (k : w64) (na : w32),
      "i" ∷ i_ptr ↦ k ∗ "Hwg" ∷ sync.join.ownAdder wg_ptr na iprop(True) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ (k = W64 0 ∨ sint.Z k ≤ sint.Z cfg.Proposers') ∧
        sint.Z na = sint.Z k⌝ : IProp GF) $$ [i Hwg]
  · iexists W64 0, W32 0
    iframe
    ipureintro
    exact ⟨by decide, Or.inl rfl, by decide⟩
  wp_for HI
  try wp_auto
  wp_if_destruct
  · have Hlt : sint.Z k < sint.Z cfg.Proposers' := by simpa using Hif
    wp_apply (sync.join.WaitGroup.wp_Add_of sync.WaitGroup.wp_Add iprop(True) wg_ptr _ na)
      $$ [Hwg] as ⟨Hwg, Hdone⟩
    · iframe; ipureintro; word
    try wp_auto
    wp_apply wp_fork $$ [Hdone]
    · try wp_auto
      wp_apply wp_Reconfigure γr _ dir c cfg.ReconfPause' sc γsc $$ [$Hcl $Hunk]
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
    refine ⟨by word, Or.inr (by word), by word⟩
  have Hk' : sint.Z k < 2 ^ 31 - 1 := by
    rcases Hk.2.1 with h | h
    · subst h; decide
    · omega
  -- the disruptions
  have Hna := Hk.2.2
  wp_join iprop(∃ na' : w32, sync.join.ownAdder wg_ptr na' iprop(True) ∗
      ⌜sint.Z na' ≤ sint.Z na + 1⌝) with [Hwg] as ⟨%na', Hwg, %Hna'⟩
  · iexists na
    iframe Hwg
    ipureintro; omega
  · wp_apply (sync.join.WaitGroup.wp_Add_of sync.WaitGroup.wp_Add iprop(True) wg_ptr _ na)
      $$ [Hwg] as ⟨Hwg, Hdone⟩
    · iframe; ipureintro; word
    try wp_auto
    wp_apply wp_fork $$ [Hdone]
    · try wp_auto
      wp_apply wp_Disrupt γr _ dir c cfg.DisruptPause' sc γsc $$ [$Hcl $Hunk]
      try wp_auto
      wp_apply (sync.join.WaitGroup.wp_Done_of sync.WaitGroup.wp_Done iprop(True) wg_ptr)
        $$ [$Hdone]
      itrivial
    try wp_auto
    wp_join_done
    iexists (na + W32 1)
    isplitl [Hwg]
    · iapply sync.join.ownAdder_wand $$ [] Hwg
      iintro _
      itrivial
    ipureintro; word
  -- the crashes: the group's resource becomes the crasher's token
  try wp_auto
  wp_join iprop(∃ na'' : w32, sync.join.ownAdder wg_ptr na'' (crasher γr)) with [Hwg Hcr]
    as ⟨%na'', Hwg⟩
  · iexists na'
    iapply sync.join.ownAdder_wand $$ [Hcr] Hwg
    iintro -
    iexact Hcr
  · wp_apply (sync.join.WaitGroup.wp_Add_of sync.WaitGroup.wp_Add (crasher γr) wg_ptr _ na')
      $$ [Hwg] as ⟨Hwg, Hdone⟩
    · iframe; ipureintro; word
    try wp_auto
    wp_apply wp_fork $$ [Hdone Hcr]
    · try wp_auto
      wp_apply wp_Crash γr _ dir c cfg.CrashPause' sc γsc $$ [$Hcl $Hcr $Hunk] as Hcr
      try wp_auto
      wp_apply (sync.join.WaitGroup.wp_Done_of sync.WaitGroup.wp_Done (crasher γr) wg_ptr)
        $$ [$Hdone $Hcr]
      itrivial
    try wp_auto
    wp_join_done
    iexists (na' + W32 1)
    iapply sync.join.ownAdder_wand $$ [] Hwg
    iintro ⟨-, H⟩
    iexact H
  -- the driver's copy of the store's state, and the invariant tying it to the client's half
  try wp_auto
  ipersist apply
  iunfold rkvVal at Hval
  icases Hval with ⟨%Hs0, Hv, %HH0⟩
  imod ghostVar_alloc (GF := GF) Hs0 with ⟨%γc, Hc⟩
  icases (ghostVar_split_half γc 1 Hs0).1 $$ Hc with ⟨Hc1, Hc2⟩
  let γd : KdNames := { γr with r := { γr.r with val := γc } }
  imod inv_alloc checkN ⊤ iprop(∃ x, rkvVal γr x ∗ rkvVal γd x) $$ [Hv Hc1] with #Hinv
  · inext
    iexists kvreconf.kvEmpty
    unfold rkvVal
    isplitl [Hv]
    · iexists Hs0; iframe; ipureintro; exact HH0
    · iexists Hs0; iframe; ipureintro; exact HH0
  wp_apply wp_Model as %m #Hm
  ihave #Hlpkg : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest
    $$ []
  · iPkgInit
  wp_apply wp_lintestRun KVMap kvS m _ _ clock kvInOk (rkvVal γd) clockVal t0 checkMask Eclk
    cfg.Clients' cfg.Ops' (W64 0) lintestN_checkMask HN Hc0 Hc31 Hops Hmul $$ [Hc2 Ht0]
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
        ihave HAU' := kdAu_of_run γr γd x (fun s => kvUpd s x.Key' x.Val') (fun _ => [])
          _
          (fun s => by unfold inStep; rw [ite_eq_left Hif])
          (fun s => by unfold inOut; rw [ite_eq_left Hif]) $$ Hinv HAU
        wp_apply wp_Put γr _ dir c x.Key' x.Val'
          _
          Hk Hv $$ [$Hcl $HAU'] as HΨ
        try wp_auto
        iapply HΨ
        iframe Htt
        ipureintro; exact ⟨⟨x, rfl⟩, [], rfl⟩
      replace Hnp : ¬ x.Kind' = opPutB := Hif
      wp_if_destruct
      · -- Get
        replace Hif : x.Kind' = opGetB := Hif
        ihave HAU' := kdAu_of_run γr γd x (fun s => s) (fun s => s x.Key')
          _
          (fun s => by unfold inStep; rw [ite_eq_right Hnp])
          (fun s => by unfold inOut; rw [ite_eq_right Hnp]) $$ Hinv HAU
        wp_apply wp_Get γr _ dir c x.Key'
          (fun v => iprop(kvS.ioOk (GF := GF) (boxIn x) (boxS v) ∗
            @threadTok GF GooseGlobalGS.gooseAllG _ -∗ Φ' #(boxS v)))
          Hk $$ [$Hcl $HAU'] as %v HΨ
        try wp_auto
        iapply HΨ
        iframe Htt
        ipureintro; exact ⟨⟨x, rfl⟩, v, rfl⟩
      · -- Read
        replace Hng : ¬ x.Kind' = opGetB := Hif
        ihave HAU' := kdAu_of_run γr γd x (fun s => s) (fun s => s x.Key')
          _
          (fun s => by unfold inStep; rw [ite_eq_right Hnp])
          (fun s => by unfold inOut; rw [ite_eq_right Hnp]) $$ Hinv HAU
        wp_apply wp_Read γr _ dir c x.Key'
          (fun v => iprop(kvS.ioOk (GF := GF) (boxIn x) (boxS v) ∗
            @threadTok GF GooseGlobalGS.gooseAllG _ -∗ Φ' #(boxS v)))
          Hk $$ [$Hcl $HAU'] as %v HΨ
        try wp_auto
        iapply HΨ
        iframe Htt
        ipureintro; exact ⟨⟨x, rfl⟩, v, rfl⟩
    isplitr
    · -- `gen`
      unfold lintest.genSpec
      iintro %id
      iintro !> %Φ' _ HΦ'
      wp_apply wp_Gen as %i #Hi
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
  wp_apply (sync.join.WaitGroup.wp_Wait_of sync.WaitGroup.wp_Wait _ na'' wg_ptr) $$ [$Hwg]
    as ⟨Hcr, -⟩
  try wp_auto
  iapply HΦ
  isplitr
  · ipureintro; rfl
  iexists γr, _
  iframe Hcr
  iframe #

end proof

end kvdurable
end EtcdGrove
end Perennial
