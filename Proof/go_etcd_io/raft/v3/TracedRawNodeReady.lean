/-
Lean-first (no Rocq counterpart). **`RawNode.Ready` at a traced node** (2026-11-11, trace-check Q8 stage 1
slice 28n; `notes/decisions.md`, "Q8 stage 1 (slice 28n)"). Raft-internal (not on `etc/api/raft.txt`).

`RawNode.Ready.spec` keeps its untraced premise (`γ.reTrace = none`) and its statement; its two halves'
specs are one for both modes since slice 28n (`readyWithoutAccept` logs nothing; `acceptReady` logs
the `Ready` line and hands out a token per message, `readyTok`). Here the traced triple: the same
triple at a traced cluster, with the term ceiling and the receipts' fit (the `Ready` line's numbers
within the trace's bound), and each handed-out message's token (`recvTokOf`, which the node API passes
to the message's `Step` at its receiver). The proof is `RawNode.Ready.wp_proof`'s over the same specs.
-/
module

public import Spec.go_etcd_io.raft.v3.RawNode__Ready
public import Spec.go_etcd_io.raft.v3.RawNode__readyWithoutAccept
public import Spec.go_etcd_io.raft.v3.RawNode__acceptReady
import Proof.go_etcd_io.raft.v3.Protocol.Enter

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

section traced
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`RawNode.Ready` at a traced node** (see the file header): `RawNode.Ready.spec`'s triple at
`γ.reTrace = some γd`, with the term ceiling below the trace's bound and the receipts' fit, and the
handed-out messages' tokens. -/
abbrev RawNode.Ready.tracedTriple : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (q : Qp) (g : Nat) (γd : GName),
  rs.steps = [] →
  rs.unpersisted = [] →
  γ.reTrace = some γd →
  uint.Z rs.tc + 1 < traceNumBound →
  receiptBound GF + γ.reBoot.length ≤ traceNumBound →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs ∗
      "Hlive" ∷ slotLive γ id q g ∗ "Hfree" ∷ slotFree γ id g }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"Ready")) (Val #()))
  {{ (rd : Ready) (ce es : List EntryM) (ms : List QMsg)
      (sts : List ReadStateM) (h : HardStateM) (steps : List Pending) (L : Option SnapLoan)
      (ss : Option (w64 × StateType)) (W : DurMaps), RET #rd;
      "Hrn" ∷ ownRawNode γ rn id
        { rs with delivered := rs.delivered ++ ce, unpersisted := es, steps := steps,
                  outlb := 0, unst := false, phs := phsNext rs.phs h, psnap := false,
                  slent := L, dur := readyDurable rs.dur (phsNext rs.phs h) L es,
                  role := roleAfter rs.role ss, bw := W } ∗
      "Hlive" ∷ slotLive γ id q g ∗
      "Henter" ∷ (∀ (E : CoPset) (q' : Qp), ⌜↑(raftN γ) ⊆ E⌝ -∗
        ownDurGhost γ id rs.dur ∗ slotLive γ id q' g ={E}=∗
          ownDurGhost γ id (readyDurable rs.dur (phsNext rs.phs h) L es) ∗ slotLive γ id q' g ∗
          slotFree γ id g ∗ durFrags γ id W ∗ [∗list] q ∈ ms, isRaftMsg γ id q.st) ∗
      "#Hlead" ∷ (⌜roleAfter rs.role ss = StateLeader⌝ -∗ [∗list] q ∈ ms, isRaftMsg γ id q.st) ∗
      "#Hss" ∷ softStateIs rd.SoftState' ss ∗
      "#Hce" ∷ entsRO rd.CommittedEntries' ce ∗
      "#Hcommitted" ∷ isCommitted γ (rs.delivered ++ ce) ∗
      "#Hents" ∷ entsRO rd.Entries' es ∗
      "Hmsgs" ∷ rd.Messages' ↦* ms.map QMsg.loc ∗
      "Hmsgs_cap" ∷ ownSliceCap Loc rd.Messages' (DFrac.own 1) ∗
      "Hmsgs_own" ∷ ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st) ∗
      "Hmsgs_cred" ∷ ([∗list] q ∈ ms,
        rdCred γ (if q.st.msg.Type' = MsgReadIndex then 1 else 0)) ∗
      "%Hmsgs_term" ∷ ⌜∀ q ∈ ms, uint.Z q.st.msg.Term' ≤ uint.Z rs.tc⌝ ∗
      "Hsnapz" ∷ rdSnapOut γ rs rd ce es L ∗
      "%Hpsn" ∷ ⌜rs.psnap = false → L = none⌝ ∗
      "#Hrs" ∷ readStatesPts rd.ReadStates' sts ∗
      "#Hrs_ok" ∷ ([∗list] st ∈ sts, readStateRaw γ st) ∗
      "#Hhard" ∷ hsOpt rd.HardState' h ∗
      "#Hhsw" ∷ hsWit γ (phsNext rs.phs h) (dlvAfter rs.delivered ce L).length ∗
      "Happ" ∷ readyOut rs.storage rs.sn es L ∗
      "#Hfrz" ∷ (⌜L ≠ none⌝ ∨ ceFrozen rs.storage rs.delivered.length ce es) ∗
      "#Hdk" ∷ dlvKeysAt rs.sn rs.delivered.length
        ((dlvAfter rs.delivered ce L).drop rs.delivered.length) ∗
      -- the `Ready` line's tokens, one per handed-out message (`acceptReady`'s `readyTok`)
      "Htoks" ∷ [∗list] q ∈ ms, recvTokOf γd q.st.msg q.st.ents q.st.ctx }}

/-- See `RawNode.Ready.tracedTriple`: `RawNode.Ready.wp_proof`'s composition, `acceptReady`'s tokens
read at the traced cluster. -/
theorem RawNode.Ready.traced
    (wp_RawNode_readyWithoutAccept : RawNode.readyWithoutAccept.spec (GF := GF) (hG := hG))
    (wp_RawNode_acceptReady : RawNode.acceptReady.spec (GF := GF) (hG := hG)) :
    RawNode.Ready.tracedTriple (GF := GF) (hG := hG) := by
  intro γ rn id rs q g γd Hsteps0 Hunp0 HtrG Htcb Hfit
  wp_start as H
  iNamed H
  wp_auto
  wp_apply wp_RawNode_readyWithoutAccept γ rn id rs Hsteps0 Hunp0 $$ [$Hrn]
    as %rd %ce %es %ms %sts %h %L H
  iNamed H
  imod ownRawNodeReady_handout ⊤ γ rn id rs rd ce es ms L q g h CoPset.subseteq_top
    $$ Hhard Hlive Hfree Hrn
    with ⟨%W, %ss0, Hrn, Happ, #Hfrz, #Hdk, Hcr, -, -, Hlive, Hpb, #Hss0, %Hssn0, #Hmw, #Hml, -⟩
  wp_apply wp_RawNode_acceptReady γ rn id { rs with bw := W } rd ce es ms h L
    (fun _ => ⟨Htcb, Hfit⟩) $$ [$Hrn $Hhard]
    as %steps %ss H
  iNamed H
  ihave %Hsseq := softStateIs_agree rd.SoftState' ss0 ss Hssn0 Hssn $$ [Hss0 Hss]
  · iframe Hss0 Hss
  subst Hsseq
  iapply HΦ $$ %rd %ce %es %ms %sts %h %steps %L %ss0 %W
  iframe Hss Hce Hcommitted Hents Hmsgs Hmsgs_cap Hmsgs_own Hcr Happ Hrs Hrs_ok Hhard Hhsw
    Hsnapz Hfrz Hdk Hlive
  isplitl [Hrn]
  · iExactEq Hrn; rfl
  isplitl [Hpb]
  · iintro %E %q' %HE ⟨Hd, Hl⟩
    imod raft_enter E γ id rs.dur q' g (readyDurable rs.dur (phsNext rs.phs h) L es) W HE
      (RaftState.next_wcommit _ _ _ _ _ _) $$ Hd Hl Hpb
      with ⟨Hd, Hl, Hf, #Hfr⟩
    imodintro
    iframe Hd Hl Hf Hfr
    iapply bigSepL_wand_pers (durFrags (GF := GF) γ id W) (fun q : QMsg => isRaftMsg γ id q.st) ms
      $$ Hmw Hfr
  isplitr
  · iexact Hml
  isplitr
  · ipureintro; exact Hmsgs_term
  isplitr
  · ipureintro; exact Hpsn
  simp only [readyTok, HtrG]
  iexact Htoks

end traced

end EtcdGrove
end Perennial
