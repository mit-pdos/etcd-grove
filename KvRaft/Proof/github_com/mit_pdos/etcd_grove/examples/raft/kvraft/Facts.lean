/-
# The protocol's facts at the store (2026-11-22; notes/kvraft-protocol.md, the table)

`kvFacts γ cf`: the instance of the wire protocol's `KvFacts` (`Proto.lean`) at the store's names `γ`
(the shared store module's `KdNames`, `Store.lean`), what each frame carries:

* a peer frame's message: sent by `src` (`sentMsg`), with its credits, persistent at a cluster with
  `dup = true` (`□ msgCredits`), and of a shape `getMsg` reads back (`MsgWf`: what the frame's reader
  needs; the sender gets it from raft's `Ready`);
* a proposal's datum: a minted operation (`d ↪[γ.r.ops]□ γp`, what `Replica.propose` takes);
* a read's `(id, seq, key)`: the context `readCtxB id seq key` minted at `(id, seq)` (kvdurable's
  `kd_mint_next`, here by the client), committed (`isReadCtx`) after a committed log `l0`
  (`readCtxAfter`), the key of a Go string's length;
* a conf change's payload: `cf` (the store's conf policy's requirement, a parameter until `confLaw`);
* the answers: `waitP` (an operation's value in a committed history) and, for a read, the key's value in
  a committed history extending `l0`'s.

`kvRep γ vs dir`: the replica the server's node runs (`isRep`, persistent).
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.DefsLaws
public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Proto

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open raft_kvreconf (readCtxB logHist kvFold)
open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section facts
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

/-- A read's facts (see the file header). -/
def readOkK (γ : KdNames) (id seq : w64) (key : List w8) : IProp GF :=
  iprop(⌜(key.length : Int) < 2 ^ 61⌝ ∗ (id, seq) ↪[γ.r.rmint]□ readCtxB id seq key ∗
    isReadCtx γ.r.cluster kdRaftN (readCtxB id seq key) (fun _ => iprop(True)) ∗
    ∃ l0 : List LogEntry, readCtxAfter γ.r.cluster kdRaftN (readCtxB id seq key) l0 ∗
      isCommittedLogLb γ.r.cluster l0)

/-- A read's answer (see the file header). -/
def ansReadK (γ : KdNames) (id seq : w64) (key v : List w8) : IProp GF :=
  iprop(∃ (l0 : List LogEntry) (L : List (List w8)),
    readCtxAfter γ.r.cluster kdRaftN (readCtxB id seq key) l0 ∗ kvLb γ L ∗
    ⌜logHist l0 <+: L ∧ v = kvFold L key⌝)

/-- A peer frame's message (see the file header). -/
def msgOkK (γ : KdNames) (src : w64) (st : MsgSt) : IProp GF :=
  iprop(sentMsg γ.r.cluster kdRaftN src st ∗ □ msgCredits γ.r.cluster kdRaftN st ∗ ⌜MsgWf st⌝)

instance readOkK_persistent (γ : KdNames) (id seq : w64) (key : List w8) :
    Persistent (readOkK (GF := GF) γ id seq key) := by
  unfold readOkK; infer_instance

instance ansReadK_persistent (γ : KdNames) (id seq : w64) (key v : List w8) :
    Persistent (ansReadK (GF := GF) γ id seq key v) := by
  unfold ansReadK; infer_instance

instance msgOkK_persistent (γ : KdNames) (src : w64) (st : MsgSt) :
    Persistent (msgOkK (GF := GF) γ src st) := by
  unfold msgOkK; infer_instance

/-- **The protocol's facts at the store** (see the file header). -/
def kvFacts (γ : KdNames) (cf : List w8 → Prop) : KvFacts GF where
  msgOk := msgOkK γ
  opOk := fun d => iprop(∃ γp : GName × GName, d ↪[γ.r.ops]□ γp)
  readOk := readOkK γ
  confOk := cf
  ansOp := waitP γ
  ansRead := ansReadK γ
  msgOk_pers := fun src st => by unfold msgOkK; infer_instance
  opOk_pers := fun d => by infer_instance
  readOk_pers := fun id seq key => by unfold readOkK; infer_instance
  ansOp_pers := fun d v => by infer_instance
  ansRead_pers := fun id seq key v => by unfold ansReadK; infer_instance
  msgOk_wf := fun src st => by
    unfold msgOkK
    iintro ⟨-, -, %H⟩
    ipureintro; exact H

/-- **The server's replica** (`Node.handle`'s `rep`): some incarnation of replica `id`, running. -/
def kvRep (γ : KdNames) (vs : List w64) (dir : GoString) (r : Loc) (id : w64) : IProp GF :=
  isRep γ vs dir id r

instance kvRep_persistent (γ : KdNames) (vs : List w64) (dir : GoString) (r : Loc) (id : w64) :
    Persistent (kvRep (GF := GF) γ vs dir r id) := by
  unfold kvRep; infer_instance

end facts

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [Net.NetProtoGS]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

/-- **The step law at the store's facts** (2026-11-22; `stepLaw`, `TransportDefs.lean`, the transport's
seam to raft's `Step`): a peer frame's message (`kvFacts`' `msgOk`: sent, its credits, well formed),
addressed to `id`, steps at `id`, at an untraced cluster with no bound on proposed data and no snapshot
directories (the store's cluster: `kdCluster`, `isReplica`'s `Hmd`, kvreconf's `DefsCluster`'s `Hsl`):
raft's `stepIn_intro`, with the sent token `sentTok_untraced` and the snapshot's locality
`snapLocalMsg_noDir`. -/
theorem kv_stepLaw (γ : KdNames) (cf : List w8 → Prop) (id : w64)
    (htr : Cluster.trace γ.r.cluster = none) (hmd : γ.r.cluster.maxData = none)
    (hsl : γ.r.cluster.snapLoc id = none) :
    ⊢ stepLaw (GF := GF) (kvFacts γ cf) γ.r.cluster kdRaftN id := by
  unfold stepLaw
  iintro !> %src %st %ml %Hto Hok Hml
  simp only [kvFacts]
  iunfold msgOkK at Hok
  icases Hok with ⟨#Hsent, #Hcr, %Hwf⟩
  icases (msgPtsC_iff_CC ml _ _ _ _).1 $$ Hml with ⟨%c, Hc, %Hcm⟩
  ihave Hs : iprop(|==> stepIn γ.r.cluster kdRaftN id ml) $$ [Hc]
  · iapply stepIn_intro γ.r.cluster kdRaftN id ml src st c Hto (by rw [Hcm.1]) Hcm.2
      (fun b hb => by rw [hmd] at hb; cases hb)
    iframe Hsent Hc Hcr
    isplitr
    · iapply snapLocalMsg_noDir γ.r.cluster id hsl st
    · iapply sentTok_untraced γ.r.cluster st htr
  imod Hs
  imodintro
  iexact Hs

end laws

end kvraft
end EtcdGrove
end Perennial
