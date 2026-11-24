/-
Probe A's steps over raft's linked traced `node.Advance` (`advance_spec_of_traced`, `probeA_round`):
moved out of `ProbeA.lean` (2026-11-18) so that its definitions, which the harness's specs name,
import no linked result (CLAUDE.md, "Import tiers"). See `ProbeA.lean`'s header.
-/
module

public import RaftTla.Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.ProbeA
public import RaftTla.Proof.go_etcd_io.raft.v3.TracedLinked

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace TraceCheck
namespace ProbeA

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

/-! ## The harness's vocabulary (§1.1, §2.2), as the design writes it -/

section claim
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (2026-11-12) **`node.Advance.spec` is `node.Advance.tracedSpec`'s instance** (A5): raft's
`node.Advance.spec_of_traced`, at the linked traced proof. -/
theorem advance_spec_of_traced : node.Advance.spec (GF := GF) (hG := hG) :=
  node.Advance.spec_of_traced RaftLink.node.wp_Advance_traced

/-- **One round of `app`, from the `Ready` to `Advance`'s return** (§2.3): the received `Ready`
(`readyGotT`), *enter* run with the driver's durable state and its share of `nodeRunning`, the snapshot
loan refuted (`probeA_noSnap`), `handleReady`'s storage and apply work (abstracted: `Hwork`, from the
`Ready`'s storage part, the batch's receipt and the view with the skipped conf entries: not on the
probe's list), then the linked `node.Advance.tracedSpec` with the claim. Its post: for each message,
what `send` takes (`probeA_msgs`), or the node stopped. -/
theorem probeA_round (n : NodeH) (γ : Cluster) (N : Namespace) (id : w64)
    (st : NodeDriverState) (rd : Ready) (qr : Qp) (hN : ↑N ⊆ (⊤ : CoPset)) :
    ⊢ notCrashed -∗ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 -∗ isCluster γ N -∗ isNode n γ N id -∗
      tcSnapsInv γ -∗ readyGotT n γ N id st rd -∗
      raftState γ id st.durable -∗ nodeRunning n γ N qr -∗
      (∀ (ce : List LogEntry) (es : List EntryM), readySnap γ N id rd st ce es none -∗
        advReceipt st.storage (st.delivered ++ ce).length es none ∗
        ∃ v : ConfigView, nodeConfig n γ N v ∗
          confAt γ (max v.applied (st.delivered ++ ce).length) v.membership) -∗
      |={⊤}=> notCrashed ∗ ∃ (ms : List QMsg) (S : RaftState), rd.Messages' ↦* ms.map QMsg.loc ∗ raftState γ id S ∗
        nodeRunning n γ N qr ∗
        WP (App (Val (n.loc @!! go.GoType.PointerType node.ty @!! go!"Advance")) (Val #()))
          {{ v, ⌜v = #()⌝ ∗ ((∃ st', nodeDriver n γ N st' ∗
              [∗list] q ∈ ms, (msgOwn q.loc (readyDq q.st) q.st ∗ sentMsg γ N id q.st ∗
                msgCredits γ N q.st) ∗ trTok γ q.st) ∨
            (∃ st', nodeStopped n γ N ∗ nodeDriver n γ N st')) }} := by
  iintro Hnc #Hi #Hc #Hn #Hsn Hrg Hrs Hrun Hwork
  ihave Hsp := probeA_readySplit n γ N id st rd $$ Hrg
  icases Hsp with ⟨%ce, %es, %h, %L, %ms, %ss, Hmsl, Hms, Hsnap, Hent, Hcl, %Hh⟩
  cases L with
  | some l =>
    imod probeA_noSnap γ N id rd st ce es l ⊤ (fun _ _ => CoPset.mem_full) $$ Hc Hsn Hsnap
      with %Hf
    exact Hf.elim
  | none =>
  iunfold readyEnter at Hent
  icases Hent with ⟨Hent, -⟩
  iunfold readyEnterLive at Hent
  imod Hent $$ %⊤ %qr %hN Hnc [Hrs Hrun] with ⟨Hnc, Hrs, Hrun, Hdrv, #Hsent⟩
  · iframe Hrs Hrun
  ihave ⟨Hrec, %v, Hv, #Hsk⟩ := Hwork $$ %ce %es Hsnap
  imodintro
  iframe Hnc
  iexists ms, _
  iframe Hmsl Hrs Hrun
  iapply (RaftLink.node.wp_Advance_traced n γ N id (st.afterReady ce es h none ss) es none v ms Hh
    (fun _ h => by cases h)) $$ [Hdrv Hrec Hv Hcl] [Hms]
  · iframe Hi Hc Hn Hdrv Hv Hcl
    simp only [NodeDriverState.afterReady]
    iframe Hrec Hsk
  · inext
    iintro Hpost
    isplitr
    · ipureintro; rfl
    icases Hpost with (⟨Hd, -, -, Ht⟩ | ⟨Hs, Hd⟩)
    · ileft
      iexists _
      iframe Hd
      iapply probeA_msgs γ N id ms $$ Hms Hsent Ht
    · iright
      iexists _
      iframe Hs Hd

end claim

end ProbeA
end TraceCheck
end EtcdGrove
end Perennial
