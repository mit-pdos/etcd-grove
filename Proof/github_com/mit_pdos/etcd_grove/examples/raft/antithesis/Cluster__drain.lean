/-
Lean-first (no Rocq counterpart). #33 S4: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/Cluster__drain.lean`: a loop whose
invariant is the loop head (`nodeOwn … (.loop net₀ ps₁)`, the `by` kept); `HasReady` false ends it
(`drain_exit`); otherwise `Ready` (its *enter* under the crash token, `readyExt` growing raft's facts),
the `ready` report and the write if the hard state, the entries or the role changed (`report_au`,
`readyStep`; `Append`, `SetHardState`, `rawNode_appended`), or the silent `Ready` (`quiet_upd`,
`Quiet.silentReady`); the rest of the iteration is `DrainPhases.lean`'s `drainSend.stmt` and
`drainAdvance.stmt`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__drain
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainReadyPure
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainBounds
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainExt
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainMsgs

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
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem Cluster.drain.wp_proof
    (wp_HasReady : RawNode.HasReady.apiSpec (GF := GF) (hG := hG))
    (wp_Ready : RawNode.Ready.apiSpec (GF := GF) (hG := hG))
    (hsend : drainSend.stmt (GF := GF) (hG := hG))
    (hadv : drainAdvance.stmt (GF := GF) (hG := hG))
    (h_vote : rawNode_vote.law (GF := GF) (hG := hG)) :
    Cluster.drain.spec (GF := GF) (hG := hG) := by
  intro _ c γ n j v net₀ ps₁ q
  wp_start as ⟨#Hc, #Hn, Hown, Had, Htok⟩
  iapply wp_fupd
  ihave #Hc' := Hc
  iunfold antCluster at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, #Hcfg, %Hcok, #Hr, #Hrec, #Hro, %Hlen, #Hn0, #Hn1, #Hn2,
    #Hstop, #Hbc, #Hnj, #Hinv, %Hfits⟩
  ihave #Hrpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  wp_auto
  irename «by» => Hbp
  irename c => Hcp
  irename n => Hnp
  ihave IH : iprop(∃ (v' : AntSim.NodeView) (net : List Msg) (ps : PState),
      nodeOwn c γ j n v' (.loop net ps) ∗ ⌜v'.byE = v.byE⌝ ∗ netAdder c γ q ∗ threadTok)
      $$ [Hown Had Htok]
  · iexists v, net₀, ps₁; iframe Hown Had Htok; ipureintro; rfl
  wp_for_core
  icases IH with ⟨%v₀, %net, %ps, Hown, %Hby, Had, Htok⟩
  icases nodeOwn_loop_open c γ j n v₀ net ps $$ Hown with ⟨%rn, %rs, %ip, #Hrn, Hraw, %Hst, Hrest⟩
  wp_auto
  wp_apply wp_HasReady γ.raft.raftNames rn (AntSim.nodeId j) rs ps [] ip $$ [$Hrpkg $Hraw] as %b ⟨Hraw, %Hb⟩
  wp_if_destruct
  · obtain ⟨hrv, hR, hip⟩ := Hst
    iunfold loopRest at Hrest
    icases Hrest with ⟨%ms, %si, %cl, %applied, #Hms, Hbs, %Hsto, Hnr, Hrole, Hterm, Hvote, Hcommit,
      Hapl, Hcause, Hv, Hl, #Hlb, Hco, %hbyok, %HN⟩
    iunfold nodeRaft at Hnr
    icases Hnr with ⟨%x, %g, Hgv, Hfree, Hdur, Htlb, Hbud, %Hγ⟩
    wp_apply wp_Ready γ.raft.raftNames rn (AntSim.nodeId j) x rs ps [] ip 1 g hrv.2.2.2.2.1
      hrv.2.2.2.2.2.1 Hγ.1 $$ [$Hrpkg $Hraw $Hgv $Hfree]
      as %rd %ce %es %rms %sts %h %steps %L %ss %W %qs' %ip' Hpost
    icases Hpost with ⟨Hraw, Hlive, Henter, #Hlead, #Hsnapto, #Hsrcs, #Hss, #Hce, #Hcommitted,
      #Hents, Hmsgs, Hmsgs_cap, Hmsgs_own, -, %Hmsgs_term, -, %Hpsn, -, -, #Hhard, #Hhsw, Happ,
      #Hfrz, -, %Hout⟩
    obtain ⟨hqs', hro, hfirst, hip', hhne⟩ := Hout trivial
    have hL : L = none := hro.2.2.2.2.2.2.2.2
    subst hL
    iapply (wp_ncfupd _ _ (by rfl))
    unfold ncfupd
    iintro Hnc
    imod Henter $$ %⊤ %(1 : Qp) %CoPset.subseteq_top Hnc [$Hdur $Hlive] with
      ⟨Hnc, Hdur, Hlive, Hfree, Hdf, #Hmok⟩
    imod (fupd_mask_mono CoPset.subseteq_top
      (h_vote γ.raft.raftNames (AntSim.nodeId j) _)) $$ Hdur with ⟨#Hvt, Hdur⟩
    imodintro
    iframe Hnc
    sorry
  · have hb : b = false := by cases b; rfl; exact absurd rfl Hif
    subst hb
    obtain ⟨hP, hip⟩ := Hb rfl
    wp_if_destruct
    · try simp only [decide_true, decide_True, ↓reduceIte]
      try wp_auto
      imod drain_exit c γ j n v₀ net ps rn rs ip Hst.1 Hst.2.1 hP hip $$ [$Hinv $Hrn $Hraw $Hrest]
        with Hown
      imodintro
      iapply HΦ
      iframe Hown Had Htok
      ipureintro; exact Hby
    · exact absurd rfl ‹¬(#false : val) = #false›
