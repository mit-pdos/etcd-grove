/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/Cluster__handle.lean`, over its callees'
specs: the input's kind (`inputOk`, by cases) picks its client call: `n.step` (idle again),
`n.propose`, `n.readIndex` (the context's bytes as a string), `n.transferLeader`, `n.campaign`,
`n.unreachable` (each drained by its own `by`, not `recv`: idle again, `nodeOwn_drained_idle`); the
kinds of batches B2/B3 are not delivered (`inputOk`'s other arms).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__handle
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__step
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__propose
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__readIndex
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__transferLeader
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__campaign
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node__unreachable
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessInput

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem Cluster.handle.wp_proof
    (wp_step : node.step.spec (GF := GF) (hG := hG))
    (wp_propose : node.propose.spec (GF := GF) (hG := hG))
    (wp_readIndex : node.readIndex.spec (GF := GF) (hG := hG))
    (wp_transferLeader : node.transferLeader.spec (GF := GF) (hG := hG))
    (wp_campaign : node.campaign.spec (GF := GF) (hG := hG))
    (wp_unreachable : node.unreachable.spec (GF := GF) (hG := hG)) :
    Cluster.handle.spec (GF := GF) (hG := hG) := by
  intro _ c γ n j v inp q
  wp_start as ⟨#Hc, #Hn, Hown, Hinp, Had, Htok, %Hb1⟩
  wp_auto
  iStructNamedPrefix inp "I"
  iunfold inputOk at Hinp
  icases Hinp with (⟨%hk, %st, Hm⟩ | ⟨%hk, %data, #Hd, Hp⟩ | ⟨⟨%hk, %hr⟩, %ctx, #Hd, Hr⟩ |
    ⟨⟨%hk, %ht, %hto⟩⟩ | %hk | %hk)
  · rw [hk]
    try wp_auto
    wp_apply wp_step c γ n j v q inp.msg' st $$ [$Hpkg $Hc $Hn $Hown $Had $Htok $Hm] as %v' ⟨Hown, Had, Htok⟩
    · ipureintro; exact Hb1
    try wp_auto
    iapply HΦ; iframe Hown Had Htok
  · rw [hk]
    try wp_auto
    wp_apply wp_propose c γ n j v q inp.data' data $$ [$Hpkg $Hc $Hn $Hown $Had $Htok $Hd $Hp]
      as %v' ⟨Hown, Had, Htok, %Hby⟩
    · ipureintro; exact Hb1
    try wp_auto
    ihave Hown := nodeOwn_drained_idle c γ j n v' (by rw [Hby]; decide) $$ Hown
    iapply HΦ; iframe Hown Had Htok
  · rw [hk]
    try wp_auto
    wp_apply wp_bytes_to_string inp.data' ctx DFrac.discard $$ [Hd] as -
    · iexact Hd
    try wp_auto
    wp_apply wp_readIndex c γ n j v q ctx $$ [$Hpkg $Hc $Hn $Hown $Had $Htok $Hr]
      as %v' ⟨Hown, Had, Htok, %Hby⟩
    · ipureintro; exact ⟨Hb1, hr⟩
    try wp_auto
    ihave Hown := nodeOwn_drained_idle c γ j n v' (by rw [Hby]; decide) $$ Hown
    iapply HΦ; iframe Hown Had Htok
  · rw [hk]
    try wp_auto
    wp_apply wp_transferLeader c γ n j v q inp.to' $$ [$Hpkg $Hc $Hn $Hown $Had $Htok]
      as %v' ⟨Hown, Had, Htok, %Hby⟩
    · ipureintro; exact ⟨Hb1, ht, hto⟩
    try wp_auto
    ihave Hown := nodeOwn_drained_idle c γ j n v' (by rw [Hby]; decide) $$ Hown
    iapply HΦ; iframe Hown Had Htok
  · rw [hk]
    try wp_auto
    wp_apply wp_campaign c γ n j v q $$ [$Hpkg $Hc $Hn $Hown $Had $Htok]
      as %v' ⟨Hown, Had, Htok, %Hby⟩
    · ipureintro; exact Hb1
    try wp_auto
    ihave Hown := nodeOwn_drained_idle c γ j n v' (by rw [Hby]; decide) $$ Hown
    iapply HΦ; iframe Hown Had Htok
  · rw [hk]
    try wp_auto
    wp_apply wp_unreachable c γ n j v q inp.to' $$ [$Hpkg $Hc $Hn $Hown $Had $Htok]
      as %v' ⟨Hown, Had, Htok, %Hby⟩
    · ipureintro; exact Hb1
    try wp_auto
    ihave Hown := nodeOwn_drained_idle c γ j n v' (by rw [Hby]; decide) $$ Hown
    iapply HΦ; iframe Hown Had Htok

end proof

end AntHarness
end EtcdGrove
end Perennial
