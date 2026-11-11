/-
Lean-first (no Rocq counterpart). **`raft.Step`'s traced bundle on a follower's accepted `MsgApp` of its
term** (2026-11-11, trace-check Q8 stage 1 slice 24c, `notes/decisions.md`, "Q8 stage 1 (slice 24c)").

Raft's `handleAppendEntries` accepts a request at or above its commit index whose previous entry its log
has (`HandleAppResult`'s second exit, `maybeAppend`); the specification's receive line is
`lineEffect_appRecv` (the truncations past the first conflict, the append, `AppendEntriesAlreadyDone`),
the response's send line is skipped (`skipGate_appresp`). The line's facts: `simFx_appAccMid` at every
intermediate state (`AccMid`: `appMid` up to the receiver's server), `simFx_appAccEnd` at the end, from
raft's facts of the new log (`ownRaftGhost_appAccFacts`). The close: the new log's `LogShapeOk` (its
bootstrap terms, `newLog_pure`) and its length within the trace's bound (its last entry's receipt,
`logRecs_traceBound`).

**The bootstrap positions** (the open question of the slice, `notes/decisions.md`, "Q8 stage 1 (slice
24c)"): the specification's abstract log fixes the first `|C|` entries (the voters' configuration
entries, term `1`, `entAbs`), so the line's correspondence needs the request's entries at those
positions of term `1` (`BootTerms`). Raft's facts give its commit index past the bootstrap log
(`ownRaftGhost_bootLe`, `|γ.reBoot| ≤ committed ≤ m.Index`), so the batch is past `|γ.reBoot|`; that
`|C| ≤ |γ.reBoot|` (the bootstrap log has one entry per voter, `BootLogOk`, known when the capability is
made) is not carried by the capability, `SimIdle` or the bundle's premises. The bundle is therefore
proved for the capability's phase strengthened by it (`stepBundle_traced.onRB`), which gives
`stepBundle_traced.on` once the fact is carried (`stepBundle_traced.on_of_onRB`, from a capability
law giving it).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvAppAcc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts]

/-- `toC` of a server with its log and leader set, from `toC` of the server. -/
theorem toC_logLead (S : Etcdraft.SetIds) (x y : Etcdraft.Server) (L : List Etcdraft.Entry) (j : Etcdraft.ID)
    (h : toC S x = toC S y) :
    toC S { x with log := L, lead := j } = toC S { y with log := L, lead := j } := by
  simp only [toC] at h ⊢
  injection h with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  rw [h1, h2, h3, h6, h7, h8, h9, h10, h11, h12]

/-- `toC` of the accepted append request's last server, from `toC` of the server. -/
theorem toC_doneSrv (S : Etcdraft.SetIds) (x y : Etcdraft.Server) (L : List Etcdraft.Entry) (j : Etcdraft.ID)
    (c : Int) (h : toC S x = toC S y) : toC S (doneSrv x L j c) = toC S (doneSrv y L j c) := by
  simp only [toC, doneSrv] at h ⊢
  injection h with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  rw [h1, h2, h3, h6, h7, h8, h9, h10, h11, h12]

/-- The accepted append request's response reads the receiver's term only. -/
theorem doneResp_toC (S : Etcdraft.SetIds) (x y : Etcdraft.Server) (m : Etcdraft.Msg) (p k : Nat)
    (h : toC S x = toC S y) : doneResp x m p k = doneResp y m p k := by
  have h1 : x.currentTerm = y.currentTerm := congrArg ServerC.currentTerm h
  unfold doneResp; rw [h1]

/-- **An accepted append request's intermediate servers, up to the pinned server** (`appMid` of any
server the share stands for): the log truncated to `k` entries past a conflict, or the new log `es'`,
the leader adopted. -/
def AccMid (C0 : List w64) (a0 : Etcdraft.Server) (src : Etcdraft.ID) (log ents es' : List EntryM) (p : Nat)
    (v : Etcdraft.Server) : Prop :=
  ∃ L', ((∃ k, p ≤ k ∧ k < log.length ∧ ConflictBy ents log p k ∧ L' = log.take k) ∨ L' = es') ∧
    toC (confAbs C0) v = toC (confAbs C0) { a0 with log := logAbs C0 C0.length 1 L', lead := src }

theorem appMid_accMid (C0 : List w64) (a a0 : Etcdraft.Server) (src : Etcdraft.ID) (log ents es' : List EntryM)
    (p : Nat) (h : toC (confAbs C0) a = toC (confAbs C0) a0) (v : Etcdraft.Server)
    (hv : appMid C0 a src log ents es' p v) : AccMid C0 a0 src log ents es' p v := by
  rcases hv with ⟨k, hpk, hkl, hcf, rfl⟩ | rfl
  · exact ⟨log.take k, .inl ⟨k, hpk, hkl, hcf, rfl⟩, toC_logLead _ _ _ _ _ h⟩
  · exact ⟨es', .inr rfl, toC_logLead _ _ _ _ _ h⟩

end pure

section fx
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **An accepted append request's receive line's phase step, at a follower of its term** (raft's
`maybeAppend` succeeding: `lineEffect_appRecv`): the server to `doneSrv` (the new log, the leader
adopted, the commit raised), the response `doneResp` added, through `AccMid`. -/
theorem phaseStepR_appAcc (id : w64) (c : CfgM) (s : NState) (m : MessageM) (ents : List EntryM) (evt : w64)
    (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (a0 : Etcdraft.Server)
    (ha0 : toC (confAbs C0) a0 = cs0) (ma : Etcdraft.Msg) (hev : RecvEvTy (absMsg .app m ents) evt)
    (hto : m.To' = id) (hterm : m.Term' = s.term) (hrole : s.role = .follower)
    (hcom : uint.Z (toPState s).commit ≤ uint.Z m.Index')
    (lastnewi : w64) (es' : List EntryM)
    (happ : plogMaybeAppend (entryID.mk (W64 0) (W64 0)) (toPState s).log
      (entryID.mk m.LogTerm' (W64 (uint.nat m.Index'))) ents = some (lastnewi, es'))
    (hbe : BootTerms C0.length (uint.nat m.Index' + 1) ents)
    (hwf : ∀ (k : Nat) (x : EntryM), ents[k]? = some x → uint.Z x.Index' = (uint.nat m.Index' : Int) + k + 1)
    (hlt0 : uint.nat m.Index' = 0 → m.LogTerm' = W64 0)
    (hnw : (uint.nat m.Index' : Int) + ents.length + 1 < 2 ^ 64)
    (hb : (absMsg .app m ents).NumsBelow traceNumBound)
    (hma : TraceSim.msgAbs C0 C0.length (absMsg .app m ents) = some ma) :
    PhaseStepR id c ma (SendEvOf evt id s c (absMsg .app m ents))
      (AccMid C0 a0 (idAbs m.From') (toPState s).log ents es' (uint.nat m.Index')) (recvPhantoms ma)
      (IdlePin s C0 cs0 P0)
      (VPin C0 (toC (confAbs C0) (doneSrv a0 (logAbs C0 C0.length 1 es') (idAbs m.From')
          (min ma.commitIndex ((uint.nat m.Index' : Int) + ents.length))))
        (P0 ++ [doneResp a0 ma (uint.nat m.Index') ents.length])) := by
  rintro C cs P ⟨rfl, rfl, rfl, hI⟩ ⟨hin, hout, hC⟩ e he
  obtain ⟨a1, ha1, hR0, hs, hP, bt, bc, bl⟩ := hI
  have hdst : (absMsg .app m ents).dst = id := hto
  have he' : SendEvOf evt (absMsg .app m ents).dst s c (absMsg .app m ents) e := by
    rw [hdst]; exact he
  obtain ⟨bmt, bk, blt, bi, bmc⟩ := numsBelow_63 hb
  have hnb := recvEvTy_notBoot hev
  refine ⟨he.2.1, sendEvOf_notBoot he hnb.1 hnb.2.1 hnb.2.2.1,
    recvLine_pred C e s c _ evt ma hev he' hout bmt bi blt bk bmc hma, ?_⟩
  intro a ha
  have hR : SimServerR C C.length (toPState s) a := simServerR_toC (ha1.trans ha.symm) hR0
  have hC' : (absMsg .app m ents).dst ∈ C := by rw [hdst]; exact hC
  have hev10 : evt = W64 10 := by
    rcases hev with ⟨-, h⟩ | ⟨h, -, -⟩ | ⟨h, -⟩ | (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -, -⟩) <;> first | exact h | cases h
  subst hev10
  obtain ⟨hmt, -⟩ := msgAbs_recvTy hev hma
  have hnl : ¬ ma.term < a.currentTerm := by
    rw [hmt, hR.1]; show ¬ uint.Z m.Term' < uint.Z (toPState s).term; rw [hterm]; exact Int.lt_irrefl _
  have hph := recvPhantoms_nolow ma a hnl
  have hcx : toC (confAbs C) a = toC (confAbs C) a0 := ha.trans ha0.symm
  have hsrc : (absMsg .app m ents).src = m.From' := rfl
  refine ⟨doneSrv a (logAbs C C.length 1 es') (idAbs m.From')
      (min ma.commitIndex ((uint.nat m.Index' : Int) + ents.length)),
    [doneResp a ma (uint.nat m.Index') ents.length],
    ⟨rfl, toC_doneSrv _ _ _ _ _ _ hcx, by rw [doneResp_toC _ _ _ _ _ _ hcx]⟩, ?_, ?_⟩
  · intro x hx; simp only [List.mem_singleton] at hx; subst hx
    simp only [doneResp]
    simp only [TraceSim.msgAbs, absMsg, absMsgFrom, Msg.mkV] at hma
    injection hma with hma
    rw [← hma]; simp [hto]
  rw [← hdst]
  simp only [hph, List.append_nil, List.foldl_cons, List.foldl_nil]
  have := lineEffect_appRecv C e s c (absMsg .app m ents) a ma rfl he' hin hout hC' hR hs hrole hterm hcom
    lastnewi es' happ hbe hwf hlt0 bt bc bl bi blt bk bmc hnw hma
  rw [hsrc] at this
  exact lineEffect_mid_mono this (appMid_accMid C a a0 _ _ _ _ _ hcx)


/-- The candidate logs of an accepted append request's intermediate states: every truncation of the
old log `L`, and the new log `es'`. -/
def accLogs (L es' : List EntryM) : List (List EntryM) :=
  (List.range L.length).map (fun k => L.take k) ++ [es']

theorem mem_accLogs (L ents es' : List EntryM) (p : Nat) (L' : List EntryM)
    (h : (∃ k, p ≤ k ∧ k < L.length ∧ ConflictBy ents L p k ∧ L' = L.take k) ∨ L' = es') :
    L' ∈ accLogs L es' := by
  unfold accLogs
  rcases h with ⟨k, -, hk, -, rfl⟩ | rfl
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)
  · exact List.mem_append_right _ (List.mem_singleton_self _)

/-- **The facts of an accepted append request's receive line, at a follower of its term** (`FxPresR` at
`recvPhantoms m`, none): at every intermediate state (`AccMid`, each drawn with the vote table before the
line's end, `votesTbl_forall_list`) `simFx_appAccMid`, at the end `simFx_appAccEnd`, both related to the
line's servers by `simFx_congr`; raft's facts of the old and the new log and of the request
(`ownRaftGhost_appAccFacts`, `isMessage_app_inv`) persistent. -/
theorem fxPresR_appAcc (γ : RaftNames) (id : w64) (ma : Etcdraft.Msg) (E : TraceEv → Prop) (s : NState)
    (C0 : List w64) (cs0 cs1 : ServerC) (P0 : List Etcdraft.Msg) (r1 : Etcdraft.Msg) (a0 : Etcdraft.Server)
    (L ents es' : List EntryM) (p : Nat) (lt lastnewi : w64) (c0 T0 : Int)
    (hiC : id ∈ C0) (hdst : ma.dest = idAbs id) (hty : ma.type = .appendEntriesRequest) (hsub : ma.subtype = "app")
    (hbL : BootTerms C0.length 1 L) (hwr : PlogWfR base0 L) (hln : L.length < 2 ^ 63)
    (hcp : c0 ≤ p) (hc0 : 0 ≤ c0)
    (hprev : ma.prevLogIndex = p) (hents : ma.entries = logAbs C0 C0.length (p + 1) ents)
    (hbe : BootTerms C0.length (p + 1) ents)
    (hwf : ∀ (k : Nat) (e : EntryM), ents[k]? = some e → uint.Z e.Index' = (p : Int) + k + 1)
    (hp : p < 2 ^ 64) (hnw : (p : Int) + ents.length + 1 < 2 ^ 64)
    (happ : plogMaybeAppend (entryID.mk (W64 0) (W64 0)) L (entryID.mk lt (W64 p)) ents = some (lastnewi, es'))
    (hwr' : PlogWfR base0 es') (hln' : es'.length < 2 ^ 63)
    (src T : w64) (bL : entryID) (l fp ents0 : List EntryM) (idx lt0 : w64)
    (hTm : ma.term = uint.Z T) (hin : plogTermAt bL l idx = some lt0)
    (hsl : ents0 <+: plogFrom bL l (idx + W64 1)) (hidx1 : uint.Z idx + 1 < 2 ^ 64)
    (hidx : ma.prevLogIndex = uint.Z idx) (hents0 : ma.entries = logAbs C0 C0.length (uint.nat idx + 1) ents0)
    (cc : Int) (hcc : cc = max c0 (min ma.commitIndex ((p : Int) + ents.length))) (hccl : cc ≤ es'.length)
    (hpin : ∀ a, toC (confAbs C0) a = cs0 →
      cs1 = toC (confAbs C0) (doneSrv a (logAbs C0 C0.length 1 es') ma.source
        (min ma.commitIndex ((p : Int) + ents.length))) ∧
      r1 = doneResp a ma p ents.length ∧ ma.term = a.currentTerm ∧ a.state = Etcdraft.follower ∧
      a.commitIndex = c0 ∧ a.currentTerm = T0 ∧ a.log = logAbs C0 C0.length 1 L ∧
      toC (confAbs C0) a = toC (confAbs C0) a0) :
    logRecs (GF := GF) γ base0 L ∗ logRecs γ base0 es' ∗ leadPrefix γ src T bL l ∗ lpfull γ src T bL l fp ∗
      commitIn γ es' (W64 cc) (W64 T0) ∗ isCommitted γ (es'.take cc.toNat) ⊢
      FxPresR (GF := GF) γ id ma E (AccMid C0 a0 ma.source L ents es' p) (recvPhantoms ma)
        (IdlePin s C0 cs0 P0) (VPin C0 cs1 (P0 ++ [r1])) := by
  iintro ⟨#HL, #HN, #Hp, #Hf, #Hci, #Hcm⟩
  iunfold FxPresR
  imodintro
  iintro %C %cs %P %e %a %a' %P' %σ %hpre Htbl #Hfx
  obtain ⟨⟨rfl, rfl, rfl, -⟩, -, hcs, ⟨-, hcs', hP⟩, -, hsrv, hσa, hpv, hcq, -, hmem⟩ := hpre
  have hP' : P' = [r1] := List.append_cancel_left hP
  subst hP'
  obtain ⟨hc1, hr1, hle, hfol, hcm1, hT, hlog, ha0⟩ := hpin a hcs
  have hph : recvPhantoms ma a = [] := recvPhantoms_nolow ma a (by rw [hle]; exact Int.lt_irrefl _)
  have hσi : σ.s (idAbs id) = a := hσa
  -- every intermediate state's facts, drawn with the vote table
  icases votesTbl_forall_list γ
      (fun _ => iprop(simFx γ C σ ∗ logRecs γ base0 L ∗ logRecs γ base0 es' ∗ leadPrefix γ src T bL l ∗
        lpfull γ src T bL l fp))
      (fun L' => iprop(∀ (_ : (∃ k, p ≤ k ∧ k < L.length ∧ ConflictBy ents L p k ∧ L' = L.take k) ∨ L' = es'),
        simFx γ C (withNode σ (idAbs id)
          { σ.s (idAbs id) with log := logAbs C C.length 1 L', lead := ma.source } _root_.id _root_.id)))
      (fun L' => by
        iintro ⟨Htbl, #Hfx, #HL, #HN, #Hp, #Hf⟩
        by_cases hL' : (∃ k, p ≤ k ∧ k < L.length ∧ ConflictBy ents L p k ∧ L' = L.take k) ∨ L' = es'
        · icases simFx_appAccMid γ C σ id ma L ents es' p lt lastnewi ma.source hsrv hiC hdst
              (by rw [hσi]; exact hfol) (by rw [hσi]; exact hle) hmem (by rw [hσi]; exact hlog) hbL hwr hln
              (by rw [hσi, hcm1]; exact hcp) (by rw [hσi, hcm1]; exact hc0) hprev hents hbe hwf hp hnw happ
              hwr' hln' src T bL l fp ents0 idx lt0 hTm hin hsl hidx1 hidx hents0 L' hL'
              $$ [$Htbl $Hfx $HL $HN $Hp $Hf] with ⟨Htbl, #H⟩
          iframe Htbl
          iintro %_
          iexact H
        · iframe Htbl
          iintro %h
          exact (hL' h).elim)
      (accLogs L es') $$ [$Htbl] with ⟨Htbl, #Hmid⟩
  · imodintro
    iintro %_ %_
    iframe Hfx HL HN Hp Hf
  -- the end state's facts
  icases simFx_appAccEnd γ C σ id ma L ents es' p lt lastnewi hsrv hiC hdst (by rw [hσi]; exact hfol) hty
      (by rw [hσi]; exact hle) hsub hmem (by rw [hσi]; exact hlog) hbL hwr hln (by rw [hσi, hcm1]; exact hcp)
      (by rw [hσi, hcm1]; exact hc0) hprev hents hbe hwf hp hnw happ hwr' hln' src T bL l fp ents0 idx lt0
      hTm hin hsl hidx1 hidx hents0 cc (by rw [hσi, hcm1]; exact hcc) hccl
      $$ [$Htbl $Hfx $HL $HN $Hp $Hf] with ⟨Htbl, #H1⟩
  · rw [hσi, hT]; iframe Hci Hcm
  iframe Htbl
  isplitl
  · iapply simFx_congr γ C (withNode σ (idAbs id) (doneSrv (σ.s (idAbs id)) (logAbs C C.length 1 es') ma.source
        (min ma.commitIndex ((p : Int) + ents.length))) (fun b => b.without ma)
        (fun b => b.with (doneResp (σ.s (idAbs id)) ma p ents.length)))
      (withNode σ (idAbs id) a' (fun b => b.without ma) (fun b => ([r1] ++ recvPhantoms ma a).foldl Etcdraft.Bag.with b))
      rfl rfl (by rw [hph, hr1, hσi]; rfl)
    · intro k
      show toC σ.server (if k = idAbs id then a' else σ.s k) =
        toC σ.server (if k = idAbs id then doneSrv (σ.s (idAbs id)) (logAbs C C.length 1 es') ma.source
          (min ma.commitIndex ((p : Int) + ents.length)) else σ.s k)
      split
      · rw [hsrv, hcs', hc1, hσi]
      · rfl
    iexact H1
  · iintro %v %hv
    obtain ⟨L', hL', hvC⟩ := hv
    ihave #Hv := Hmid $$ %L' %(mem_accLogs L ents es' p L' hL')
    ihave #Hv' := Hv $$ %hL'
    iapply simFx_congr γ C (withNode σ (idAbs id)
        { σ.s (idAbs id) with log := logAbs C C.length 1 L', lead := ma.source } _root_.id _root_.id)
      (withNode σ (idAbs id) v _root_.id _root_.id) rfl rfl rfl
    · intro k
      show toC σ.server (if k = idAbs id then v else σ.s k) =
        toC σ.server (if k = idAbs id then { σ.s (idAbs id) with log := logAbs C C.length 1 L', lead := ma.source }
          else σ.s k)
      split
      · rw [hsrv, hvC, hσi]; exact (toC_logLead _ _ _ _ _ ha0).symm
      · rfl
    iexact Hv'


/-- **Raft's facts of an accepted append request at the node's step ghost** (`ownRaftGhost_appAccFacts`,
`ownRaftGhost_bootLe`, and the new log's length within the trace's bound, `logRecs_traceBound`); the ghost
state unchanged. -/
theorem ownStepGhost_appAccFacts (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState) (m : Msg)
    (lastnewi : w64) (es' : List EntryM)
    (Hty : m.ty = .app) (Hterm : m.term = s.term) (Hbase : (toPState s).base = base0)
    (Hcidx : uint.Z s.logst.committed ≤ uint.Z m.index)
    (Happ : plogMaybeAppend base0 (toPState s).log (entryID.mk m.logterm m.index) m.entries = some (lastnewi, es'))
    (Hfit : receiptBound GF + γ.reBoot.length ≤ traceNumBound) :
    isMessage (GF := GF) γ m ∗ ownStepGhost γ md c id s ⊢ |={⊤}=> ownStepGhost γ md c id s ∗
      (logRecs γ base0 (toPState s).log ∗ logRecs γ base0 es' ∗
        commitIn γ es' (accCommit (toPState s).commit m.commit lastnewi) (toPState s).term ∗
        isCommitted γ (es'.take (uint.Z (accCommit (toPState s).commit m.commit lastnewi)).toNat)) ∗
      ⌜PlogWfR base0 (toPState s).log ∧ PlogWfR base0 es' ∧ PlogWf base0 es' ∧
        uint.Z s.logst.committed ≤ (toPState s).log.length ∧
        uint.Z lastnewi = uint.Z m.index + (m.entries.length : Int) ∧
        (γ.reBoot.length : Int) ≤ uint.Z s.logst.committed ∧ (es'.length : Int) < traceNumBound⌝ := by
  iintro ⟨#Hm, Hgh⟩
  iunfold ownStepGhost at Hgh
  icases Hgh with ⟨Hg, Hr⟩
  icases ownRaftGhost_appAccFacts γ id (toPState s) m lastnewi es' Hty Hterm Hbase Hcidx Happ $$ Hm Hg with
    ⟨Hg, ⟨#HL, -, -, #HN, #Hci, #Hcm⟩, %Hp⟩
  obtain ⟨hwr, hwr', hcl, hli, hwN⟩ := Hp
  icases ownRaftGhost_bootLe γ id (toPState s) $$ Hg with ⟨Hg, %Hbt⟩
  have hlN : es'.length < 2 ^ 64 := by
    rcases Nat.eq_zero_or_pos es'.length with h0 | hpos
    · omega
    · obtain ⟨e, he⟩ : ∃ e, es'[es'.length - 1]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hi := hwN _ e he
      rw [base0_index] at hi
      have := uint_Z_lt e.Index'
      omega
  imod logRecs_traceBound γ es' hwN hlN Hfit $$ HN with %HB
  imodintro
  isplitl [Hg Hr]
  · iunfold ownStepGhost; iframe Hg Hr
  iframe HL HN Hci Hcm
  ipureintro
  exact ⟨hwr, hwr', hwN, hcl, hli, Hbt, HB⟩

/-- **The idle relation after an accepted append request at a follower of its term**: raft's end state
(the leader adopted, the new log and commit index, the response queued) is related to the
specification's (`doneSrv`, `doneResp`). -/
theorem accEnd_simIdle (C : List w64) (id : w64) (s : NState) (m : MessageM) (a0 : Etcdraft.Server)
    (ma : Etcdraft.Msg) (ls' : LogState) (es' : List EntryM) (lastnewi : w64) (p k : Nat)
    (hR : SimServerR C C.length (toPState s) a0) (hs : LogShapeOk C.length (toPState s))
    (bt : uint.Z s.term < 2 ^ 63) (hrole : s.role = .follower)
    (hprev : ls'.prev = s.logst.prev) (hes : ls'.sents ++ ls'.uents = es')
    (hcm : ls'.committed = accCommit s.logst.committed m.Commit' lastnewi)
    (hbN : BootTerms C.length 1 es') (hwN : PlogWf base0 es') (hB : (es'.length : Int) < traceNumBound)
    (hli : uint.Z lastnewi = (p : Int) + k) (hlast : uint.Z lastnewi ≤ es'.length)
    (hcp : uint.Z s.logst.committed ≤ p)
    (hmc : ma.commitIndex = uint.Z m.Commit') (hmsub : ma.subtype = "app") (hmd : ma.dest = idAbs id)
    (hms : ma.source = idAbs m.From') :
    SimIdle C (sendMsgs { ({ s with lead := m.From' } : NState) with logst := ls' }
        [appResp id { s with lead := m.From' } m.From' false lastnewi (W64 0) (W64 0)])
      (toC (confAbs C) (doneSrv a0 (logAbs C C.length 1 es') (idAbs m.From') (min ma.commitIndex ((p : Int) + k))))
      (pendAbs C s.outbox ++ [doneResp a0 ma p k]) := by
  obtain ⟨hT, hSt, hV, hL, hB0, hLog, hCm, hCfg, hPc, -, -⟩ := hR
  have hb : traceNumBound = 2 ^ 61 := rfl
  have hcmZ : uint.Z ls'.committed = max a0.commitIndex (min ma.commitIndex ((p : Int) + k)) := by
    rw [hcm, hCm, hmc, ← hli]
    unfold accCommit plogCommitTo
    show _ = max (uint.Z (toPState s).commit) _
    simp only [toPState]
    repeat' split
    all_goals omega
  have hcl : uint.Z ls'.committed ≤ es'.length := by
    rw [hcmZ, hCm]; simp only [toPState]; omega
  have hB61 : (es'.length : Int) < 2 ^ 61 := by have := hB; rw [hb] at this; exact this
  refine ⟨_, rfl, ?_, ?_, ?_, bt, by show uint.Z ls'.committed < 2 ^ 63; omega, ?_⟩
  · refine ⟨by simp only [doneSrv]; rw [hT]; rfl, ?_, by simp only [doneSrv]; rw [hV]; rfl, ?_, ?_, ?_, ?_,
      by simp only [doneSrv]; exact hCfg, by simp only [doneSrv]; exact hPc, ?_, ?_⟩
    · simp only [doneSrv]; rw [hSt]; simp [toPState, sendMsgs, hrole]
    · simp [toPState, sendMsgs, hrole, doneSrv]
    · rw [← hB0]; simp [toPState, sendMsgs, hprev]
    · simp [toPState, sendMsgs, doneSrv, hes]
    · simp only [doneSrv]; rw [← hcmZ]; simp [toPState, sendMsgs]
    · intro h; simp [toPState, sendMsgs, hrole, proleRole] at h
    · intro h; simp [toPState, sendMsgs, hrole, proleRole] at h
  · obtain ⟨hs1, -, -⟩ := hs
    refine ⟨?_, ?_, ?_⟩
    · simp only [toPState, sendMsgs, hprev]; exact hs1
    · simp only [toPState, sendMsgs, hprev, hes]; rw [show s.logst.prev = base0 from hs1]; exact hwN
    · intro k e hk he
      simp only [toPState, sendMsgs, hes] at he
      exact hbN k e (by omega) he
  · show _ = pendAbs C (s.outbox ++ _)
    rw [pendAbs_append]
    simp [pendAbs, TraceSim.msgAbs, appResp, doneResp, hT, hmsub, hmd, hms, hli, toPState]
  · have h0 : (toPState (sendMsgs { ({ s with lead := m.From' } : NState) with logst := ls' }
        [appResp id { s with lead := m.From' } m.From' false lastnewi (W64 0) (W64 0)])).base = base0 := by
      simp only [toPState, sendMsgs, hprev]; exact hs.1
    unfold plastIndex plogLastIndexZ
    rw [h0, base0_index]
    simp only [toPState, sendMsgs, hes]
    word
end fx


variable [GooseExts] in
/-- An uncompacted well-formed log's length fits a word (its last entry's index). -/
theorem plogWf_len_lt (F : List EntryM) (hw : PlogWf base0 F) : F.length < 2 ^ 64 := by
  rcases Nat.eq_zero_or_pos F.length with h0 | hpos
  · omega
  · obtain ⟨e, he⟩ : ∃ e, F[F.length - 1]? = some e := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hi := hw _ e he
    rw [base0_index] at hi
    have := uint_Z_lt e.Index'
    omega

section paths
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`stepBundle_traced.on` for a capability whose voters fit the bootstrap log** (`|C| ≤ |γ.reBoot|`:
the bootstrap log has one entry per voter, `BootLogOk`, known when the capability is made but carried
by none of its clauses; `notes/decisions.md`, "Q8 stage 1 (slice 24c)"): the statement of
`stepBundle_traced.on` with the capability's phase `SimIdle C s` strengthened by it. -/
abbrev stepBundle_traced.onRB (Path : NState → MessageM → Prop) : Prop :=
  ∀ (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM)
    (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) (γd : GName)
    (Λ : Option TraceEv → Prop) (bt : Bool),
  Path s m →
  s.gh.tr = some γd →
  s.prevote = false → s.cq = false → StepEndTy m.Type' → NStateWf s →
  (m.Type' = MsgHup ∨ m.Type' = MsgBeat ∨ m.Type' = MsgProp → m.Term' = W64 0) →
  (m.Type' = MsgHup → s.role ≠ .leader) →
  (∀ ty, mtypeOf m.Type' = some ty → ty.traced = true → m.To' = id) →
  uint.Z s.term + 1 < traceNumBound → uint.Z m.Term' < traceNumBound →
  (∀ ty, mtypeOf m.Type' = some ty → MsgTrOk γ (absMsg ty m ents ctx)) →
  receiptBound GF + γ.reBoot.length ≤ traceNumBound →
  c.learners = ∅ → domSet s.progress ⊆ c.voters ∪ c.learners →
  s.role ≠ .preCandidate → TrRecvShape m ents →
  (m.Type' = MsgHeartbeat ∨ m.Type' = MsgApp → γ.reBoot ≠ []) →
  (trCapB s.gh.tr γ r id c bt (fun C cs P => SimIdle C s cs P ∧ C.length ≤ γ.reBoot.length) Λ ∗
      (recvTokOf γd m ents ctx ∗
        □ (∀ ty : MsgType, ⌜mtypeOf m.Type' = some ty ∧ ty.traced = true⌝ -∗
          isMessageC γ (absMsg ty m ents ctx))) ∗
      TrNoSnap s.gh.tr s.logst : IProp GF) ⊢
    |={⊤}=> ∃ R : StepG GF, R.G ∗ stepGates c r id s m ents sn ctx rs (ghostIn γ md c id s R) ∗
      stepClose γ md c id m ents ctx s R
        (fun s' => iprop(∃ bt' : Bool, trCapB s.gh.tr γ r id c bt' (fun C => SimIdle C s') (stepLastEv Λ)))

/-- **`stepBundle_traced.onRB` gives `stepBundle_traced.on`** once the capability gives the voters' fit
(`hcap`, a law of the capability that carries it). -/
theorem stepBundle_traced.on_of_onRB {Path : NState → MessageM → Prop}
    (hcap : ∀ (tr : Option GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (b : Bool) (s : NState)
      (Λ : Option TraceEv → Prop),
      trCapB (GF := GF) tr γ r id c b (fun C => SimIdle C s) Λ ⊢
        trCapB tr γ r id c b (fun C cs P => SimIdle C s cs P ∧ C.length ≤ γ.reBoot.length) Λ)
    (h : stepBundle_traced.onRB (GF := GF) (hG := hG) Path) :
    stepBundle_traced.on (GF := GF) (hG := hG) Path := by
  intro γ md c r id s m ents sn ctx rs γd Λ bt hp htr hpv hcq hty hwf hloc hhup hto hT hmT hok hfit hlrn hdom
    hnpc hsh hboot
  iintro ⟨Hcap, Htok, Hns⟩
  iapply h γ md c r id s m ents sn ctx rs γd Λ bt hp htr hpv hcq hty hwf hloc hhup hto hT hmT hok hfit hlrn hdom
    hnpc hsh hboot
  iframe Htok Hns
  iapply hcap $$ Hcap

/-- **An accepted append request of the node's term at a follower** (at or above the commit index, the
log matching its previous entry). -/
def FolAppAcc (s : NState) (m : MessageM) : Prop :=
  m.Type' = MsgApp ∧ m.Term' = s.term ∧ s.role = .follower ∧ uint.Z s.logst.committed ≤ uint.Z m.Index' ∧
  PlogMatches s.logst.prev (s.logst.sents ++ s.logst.uents) (entryID.mk m.LogTerm' m.Index')

/-- `maybeAppend` succeeds at a matching previous entry. -/
theorem plogMaybeAppend_some_of {b : entryID} {es : List EntryM} {prev : entryID} (ents : List EntryM)
    (h : PlogMatches b es prev) : ∃ x, plogMaybeAppend b es prev ents = some x := by
  unfold plogMaybeAppend; simp only [h, ↓reduceIte]; exact ⟨_, rfl⟩

/-- **`raft.Step`'s traced bundle on an accepted append request of the node's term at a follower**: the
receive line (the specification's truncations, append and `AppendEntriesAlreadyDone`, `lineEffect_appRecv`,
with raft's facts of the new log), then the response's send line, which the specification skips. The
resources are `voteR`'s. Proved for the capability whose voters fit the bootstrap log
(`stepBundle_traced.onRB`). -/
theorem stepBundle_traced_folAppAcc : stepBundle_traced.onRB (GF := GF) (hG := hG) FolAppAcc := by
  intro γ md c r id s m ents sn ctx rs γd Λ bfl hp htr hpv hcq hty hwf hloc hhup hto hT hmT hok hfit hlrn hdom
    hnpc hsh hboot
  obtain ⟨hTy, hterm, hrole, hge, hmt⟩ := hp
  have hmty : mtypeOf m.Type' = some .app := by rw [hTy]; rfl
  have htrd : MsgType.traced .app = true := rfl
  obtain ⟨evt, hevt, hev⟩ := recvEvTy_of .app m ents hmty htrd hsh
  have hto' : m.To' = id := hto .app hmty htrd
  have hne : id ≠ m.From' := fun h => hsh.2.2 (.inr (.inl hTy)) (by rw [hto', h])
  have hnbf : ¬ PreBF m s := fun h => absurd h.1 (by rw [hterm]; omega)
  have hpre : ∀ pvs, preState s m pvs = s := fun pvs => by simp [preState, hnbf]
  have hns : ¬ StaleMsg s m := fun h => absurd h.2 (by rw [hterm]; omega)
  have hsome : s.gh.tr ≠ none := by rw [htr]; simp
  obtain ⟨hnH, hnV, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnVR, hnHR, hnAR, hnPV, hnHup, hnS⟩ := app_ne hTy
  have hmt2 : mtypeOf m.Type' = some .app ∧ MsgType.traced .app = true := ⟨hmty, htrd⟩
  iintro ⟨Hcap, ⟨Htok, #Hmsg⟩, #Hnosnap⟩
  iunfold recvTokOf at Htok
  icases Htok $$ %MsgType.app %hmt2 with ⟨%tn, %k, %ma, #Hdir, %hma, Htok⟩
  ihave #Hmc := Hmsg $$ %MsgType.app %hmt2
  ihave #Hm := isMessageC_isMessage γ _ $$ Hmc
  icases isMessage_app_inv γ (absMsg .app m ents ctx) rfl $$ Hm with
    ⟨%Hpay, -, ⟨%bL, %l, %fpL, #Hlp, %Hpl, #Hlf, -, -, -⟩, -⟩
  icases isMessage_app_index0 γ (absMsg .app m ents ctx) rfl $$ Hm with %Hi0
  rw [msgAbs_absMsg_ctx] at hma
  rw [htr]
  icases trCapB_pinDir γd γ r id c bfl _ Λ $$ Hcap with ⟨%tn', %cs0, %P0, #Hdir', %hI0, Hcap⟩
  icases traceDir_agree γd tn tn' $$ [$Hdir $Hdir'] with %Htn
  subst Htn
  obtain ⟨⟨⟨a0, ha0, hR0, hs0, hP0, bt, bc, bl⟩, hCB⟩, hidC⟩ := hI0
  ihave Hcap := trCapB_mono (some γd) γ r id c bfl _ (IdlePin s tn.voters cs0 P0) Λ
    (fun C cs P h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩) $$ Hcap
  -- the request's abstraction
  have hfa : ma.dest = idAbs id ∧ ma.source = idAbs m.From' ∧ ma.type = .appendEntriesRequest ∧
      ma.subtype = "app" ∧ ma.term = uint.Z m.Term' ∧ ma.prevLogIndex = ((uint.nat m.Index' : Nat) : Int) ∧
      ma.entries = logAbs tn.voters tn.voters.length (uint.nat m.Index' + 1) ents ∧
      ma.commitIndex = uint.Z m.Commit' := by
    simp only [TraceSim.msgAbs, absMsg, absMsgFrom, Msg.mkV] at hma
    injection hma with hma
    rw [← hma]
    simp [hto']
  obtain ⟨hmd, hms, hmty', hmsub, hmterm, hmprev, hments, hmcm⟩ := hfa
  -- the new log
  have hbase : (toPState s).base = base0 := hs0.1
  have hmatch : PlogMatches base0 (toPState s).log (entryID.mk m.LogTerm' m.Index') := by
    rw [← hbase]; exact hmt
  obtain ⟨⟨lastnewi, es'⟩, happ⟩ := plogMaybeAppend_some_of ents hmatch
  have hWi : W64 (uint.nat m.Index') = m.Index' := by word
  have happ' : plogMaybeAppend (entryID.mk (W64 0) (W64 0)) (toPState s).log
      (entryID.mk m.LogTerm' (W64 (uint.nat m.Index'))) ents = some (lastnewi, es') := by
    rw [hWi]; exact happ
  obtain ⟨hwfE, hnwE⟩ := Hpay
  have hpZ : ((uint.nat m.Index' : Nat) : Int) = uint.Z m.Index' := by word
  have hwfZ : ∀ (k : Nat) (x : EntryM), ents[k]? = some x →
      uint.Z x.Index' = (uint.nat m.Index' : Int) + k + 1 := by
    intro k x hx
    have h2 : uint.Z x.Index' = uint.Z m.Index' + ((k + 1 : Nat) : Int) := hwfE k x hx
    rw [h2, ← hpZ]; push_cast; omega
  have hnw : (uint.nat m.Index' : Int) + ents.length + 1 < 2 ^ 64 := by
    have h2 : uint.Z m.Index' + (ents.length : Int) + 1 < 2 ^ 64 := hnwE
    rw [hpZ]; exact h2
  have hlt0 : uint.nat m.Index' = 0 → m.LogTerm' = W64 0 := fun h => Hi0 (by
    show uint.Z m.Index' = 0; have := h; word)
  have hwB : PlogWf base0 (toPState s).log := by have h := hs0.2.1; rw [hs0.1] at h; exact h
  have hbL : BootTerms tn.voters.length 1 (toPState s).log := fun k e hk he => hs0.2.2 k e (by omega) he
  have hcp : uint.Z s.logst.committed ≤ (uint.nat m.Index' : Int) := by rw [hpZ]; exact hge
  have hbN0 : ∀ (hreb : (γ.reBoot.length : Int) ≤ uint.Z s.logst.committed),
      BootTerms tn.voters.length (uint.nat m.Index' + 1) ents := by
    intro hreb k e hk _; omega
  have hT2 : uint.nat s.term < traceNumBound := by word
  imodintro
  iexists voteR bfl γ md c r id s γd tn cs0
    (toC (confAbs tn.voters) (doneSrv a0 (logAbs tn.voters tn.voters.length 1 es') (idAbs m.From')
      (min ma.commitIndex ((uint.nat m.Index' : Int) + ents.length)))) P0
    (P0 ++ [doneResp a0 ma (uint.nat m.Index') ents.length]) Λ k ma
  isplitl [Hcap Htok]
  · dsimp only [voteR]; iframe Hcap Htok
  isplitr
  · iunfold stepGates
    dsimp only [ghostIn, voteR]
    isplitr
    · -- the receive line
      iintro ⟨Hgh, Hc, Htok⟩
      iapply hookGateOpt_fupd_recv
      icases ownStepGhost_nsLink γ md c id s $$ Hgh with ⟨%Hnl, Hgh⟩
      imod ownStepGhost_traceOk γ md c id s hfit $$ Hgh with ⟨%Hb, Hgh⟩
      imod ownStepGhost_appAccFacts γ md c id s (absMsg .app m ents ctx) lastnewi es' rfl hterm hbase hge happ hfit
        $$ [$Hm $Hgh] with ⟨Hgh, ⟨#HL, #HN, #Hci, #Hcm⟩, %Hf⟩
      obtain ⟨hwr, hwr', hwN, hcl, hli, hreb, hBN⟩ := Hf
      imodintro
      have hreT : γ.reTrace.isSome := by rw [← Hnl.2.1, htr]; rfl
      have hnb : (absMsg .app m ents).NumsBelow traceNumBound := (hok .app hmty hreT htrd).1
      have hbe := hbN0 hreb
      have hps := phaseStepR_appAcc id c s m ents evt tn.voters cs0 P0 a0 ha0 ma hev hto' hterm hrole hge
        lastnewi es' happ' hbe hwfZ hlt0 hnw hnb hma
      have hnb' := recvEvTy_notBoot hev
      have hOk : ∀ e, SendEvOf evt id s c (absMsg .app m ents) e → TraceEv.Ok (elements c.incoming).length e :=
        fun e he => sendEvOf_ok evt id s c _ e _ he ⟨hnb'.1, hnb'.2.2.2⟩ (by word) Hb.2 Hb.1 hnb (Nat.le_refl _)
      iapply recvGate_traced γd γ r id c s m ents sn ctx rs .app evt bfl k ma _
        (recvPhantoms ma) _ _ Λ (ownStepGhost γ md c id s) htr hmty hevt hps hOk
      iframe Hgh Hc
      isplitr
      · have hli' : uint.Z lastnewi = (uint.nat m.Index' : Int) + ents.length := by rw [hpZ]; exact hli
        have hlast : uint.Z lastnewi ≤ es'.length := by
          obtain ⟨-, -, hq, -, -⟩ := newLog_pure tn.voters (toPState s).log ents es' (uint.nat m.Index') m.LogTerm'
            lastnewi 0 hbL hbe hwfZ (by word) hnw (Nat.zero_le _) happ'
          omega
        have hccZ : uint.Z (accCommit (toPState s).commit m.Commit' lastnewi) =
            max (uint.Z s.logst.committed) (min ma.commitIndex ((uint.nat m.Index' : Int) + ents.length)) := by
          rw [hmcm, ← hli']
          unfold accCommit plogCommitTo
          show _ = max (uint.Z (toPState s).commit) _
          repeat' split
          all_goals omega
        have hW1 : W64 (uint.Z (accCommit (toPState s).commit m.Commit' lastnewi)) =
            accCommit (toPState s).commit m.Commit' lastnewi := by word
        have hW2 : W64 (uint.Z s.term) = (toPState s).term := by
          show W64 (uint.Z s.term) = s.term; word
        have hBN' : (es'.length : Int) < 2 ^ 63 := by
          have : traceNumBound = 2 ^ 61 := rfl
          omega
        rw [← hms]
        iapply fxPresR_appAcc γ id ma _ s tn.voters cs0 _ P0 _ a0 (toPState s).log ents es' (uint.nat m.Index')
          m.LogTerm' lastnewi (uint.Z s.logst.committed) (uint.Z s.term) hidC hmd hmty' hmsub hbL hwr
          (by have h1 := bl; have h2 := plogWf_len_lt _ hwB
              unfold plastIndex plogLastIndexZ at h1; rw [hbase, base0_index] at h1
              simp only [Int.zero_add] at h1
              have : uint.Z (W64 ((toPState s).log.length : Int)) = (toPState s).log.length := by word
              omega)
          hcp (uint_Z_nonneg _) hmprev hments hbe hwfZ (by word) hnw happ' hwr' (by omega)
          (absMsg .app m ents ctx).src (absMsg .app m ents ctx).term bL l fpL ents m.Index' m.LogTerm' hmterm
          Hpl.1 Hpl.2
          (by have h2 : uint.Z m.Index' + (ents.length : Int) + 1 < 2 ^ 64 := hnwE; omega) (by rw [hmprev, hpZ]) hments
          (uint.Z (accCommit (toPState s).commit m.Commit' lastnewi)) hccZ (by
            rw [hccZ]; have := hcl; omega)
        · intro a ha
          have hcx : toC (confAbs tn.voters) a0 = toC (confAbs tn.voters) a := ha0.trans ha.symm
          have hRa : SimServerR tn.voters tn.voters.length (toPState s) a := simServerR_toC hcx hR0
          refine ⟨by rw [hms]; exact toC_doneSrv _ _ _ _ _ _ hcx, doneResp_toC _ _ _ _ _ _ hcx,
            by rw [hmterm, hRa.1, hterm]; rfl, ?_, hRa.2.2.2.2.2.2.1, by rw [hRa.1]; rfl, hRa.2.2.2.2.2.1, hcx.symm⟩
          rw [hRa.2.1]; simp [toPState, hrole, proleRole, roleAbs]
        · rw [hW1, hW2, show (absMsg .app m ents ctx).commit = m.Commit' from rfl]
          iframe HL HN Hlp Hlf Hci Hcm
      · iexists tn; iframe Hdir Htok
    isplitr
    · -- the preamble: no step-down at the node's term
      unfold preGate
      iintro %_ HG0
      simp only [hnbf, ↓reduceIte]
      imodintro
      iexact HG0
    isplitr
    · iintro %h; exact (hns h).elim
    isplitr
    · iintro %h; exfalso; rcases h with h | h
      · exact hnV h
      · exact hnPV h
    isplitr
    · iintro %h; exact (hnHup h).elim
    isplitr
    · unfold stepFnGates
      iintro %pvs
      rw [hpre pvs]
      isplit
      · iintro %_
        iunfold followerGates
        isplitr
        · -- the response's send line, skipped by the specification
          iintro %_ %s1 %mm %hres ⟨Hgh, Hc⟩
          have hx : ∃ ls' : LogState, s1 = { ({ s with lead := m.From' } : NState) with logst := ls' } ∧
              mm = appResp id { s with lead := m.From' } m.From' false lastnewi (W64 0) (W64 0) ∧
              ls'.prev = s.logst.prev ∧ ls'.sents ++ ls'.uents = es' ∧
              ls'.committed = accCommit s.logst.committed m.Commit' lastnewi := by
            unfold HandleAppResult at hres
            try simp only at hres
            rcases hres with ⟨h, -⟩ | ⟨-, ln2, es2, ls', h2, hp', hes2, -, hc2, -, -, h⟩ | ⟨-, hnm, -⟩
            · exact absurd h (by omega)
            · rw [show s.logst.prev = base0 from hbase] at h2
              have h3 := h2.symm.trans happ
              simp only [Option.some.injEq, Prod.mk.injEq] at h3
              obtain ⟨rfl, rfl⟩ := h3
              obtain ⟨h1, h4⟩ := sendMsgs_one_inj h
              exact ⟨ls', h1, h4, hp', hes2, by rw [hc2]; rfl⟩
            · exact absurd hmt hnm
          obtain ⟨ls', rfl, rfl, hprev', hes', hcm'⟩ := hx
          rw [htr]
          iapply hookGateOpt_fupd_recv
          icases ownStepGhost_nsLink γ md c id s $$ Hgh with ⟨%Hnl, Hgh⟩
          imod ownStepGhost_appAccFacts γ md c id s (absMsg .app m ents ctx) lastnewi es' rfl hterm hbase hge happ hfit
            $$ [$Hm $Hgh] with ⟨Hgh, -, %Hf⟩
          obtain ⟨hwr, hwr', hwN, hcl, hli, hreb, hBN⟩ := Hf
          imodintro
          have hli' : uint.Z lastnewi = (uint.nat m.Index' : Int) + ents.length := by rw [hpZ]; exact hli
          have hb61 : traceNumBound = 2 ^ 61 := rfl
          have hlast : uint.Z lastnewi ≤ es'.length := by
            obtain ⟨-, -, hq, -, -⟩ := newLog_pure tn.voters (toPState s).log ents es' (uint.nat m.Index') m.LogTerm'
              lastnewi 0 hbL (hbN0 hreb) hwfZ (by word) hnw (Nat.zero_le _) happ'
            omega
          have hacc : uint.Z (accCommit s.logst.committed m.Commit' lastnewi) ≤ es'.length := by
            unfold accCommit plogCommitTo
            have : (uint.nat m.Index' : Int) = uint.Z m.Index' := hpZ
            repeat' split
            all_goals omega
          have hn := appResp_nums id { s with lead := m.From' } m.From' lastnewi hT (by
            show uint.nat lastnewi < traceNumBound; have := uint_Z_nonneg lastnewi; rw [hb61] at hBN ⊢; word)
          have ht2 : uint.nat s.term < traceNumBound := by word
          have hc1 : uint.nat ({ ({ s with lead := m.From' } : NState) with logst := ls' } : NState).logst.committed
              < traceNumBound := by
            show uint.nat ls'.committed < traceNumBound
            rw [hcm']; have := uint_Z_nonneg (accCommit s.logst.committed m.Commit' lastnewi)
            rw [hb61] at hBN ⊢; word
          have hl1 : uint.nat (plastIndex (toPState ({ ({ s with lead := m.From' } : NState) with logst := ls' } :
              NState))) < traceNumBound := by
            unfold plastIndex plogLastIndexZ
            show uint.nat (W64 (uint.Z ls'.prev.index' + ((ls'.sents ++ ls'.uents).length : Int))) < traceNumBound
            rw [hprev', hes', show s.logst.prev = base0 from hbase, base0_index]
            rw [hb61] at hBN ⊢
            have h0 : (0 : Int) + (es'.length : Int) < 2 ^ 61 := by omega
            word
          have hOkR : ∀ e, (∃ mm ∈ [appResp id { s with lead := m.From' } m.From' false lastnewi (W64 0) (W64 0)],
              SendEvOf (W64 11) id { ({ s with lead := m.From' } : NState) with logst := ls' } c mm e) →
              TraceEv.Ok (elements c.incoming).length e := by
            intro e ⟨mm, hmm, he⟩
            simp only [List.mem_singleton] at hmm; subst hmm
            exact sendEvOf_ok _ id _ c _ e _ he (by decide) ht2 hc1 hl1 hn (Nat.le_refl _)
          iapply skipGate_appresp γd γ r id c _ _ tn.voters _ _ (ownStepGhost γ md c id s) rfl
            (by simp only [appResp]; exact hne) hOkR
          iframe Hgh Hc
        isplitr; · iintro %hg; exact (hnH hg).elim
        isplitr
        · iintro %hg
          rcases hg with h | h | h
          · exact (hnP h).elim
          · exact (hnRI h).elim
          · exact (hnTL h).elim
        isplitr; · iintro %hg; exact (hnTN hg).elim
        imodintro; iintro %hg; exact (hnTN hg).elim
      isplit
      · iintro %h; exfalso; rw [hrole] at h; rcases h with h | h <;> cases h
      · iintro %h; exfalso; rw [hrole] at h; cases h
    · ipureintro
      exact ⟨fun _ _ _ => rfl, IdxFree.of_some _ hsome, IdxFree.of_some _ hsome,
        IdxFree.of_some _ hsome, fun _ _ => IdxFree.of_some _ hsome⟩
  · -- the closing wand: raft's accepted append, the specification's
    iapply stepClose_anyB
    -- (slice 23a) a close at `s`
    iapply stepClose_of_at _ _ _ _ _ _ _ _ _ _ (fun _ => CloseAt.of_traced hmty rfl)
    iunfold stepCloseAt
    iintro %s' %B %recv %_ %hend Hout
    obtain ⟨ls', hse, hprev', hes', hcm'⟩ : ∃ ls' : LogState,
        s' = sendMsgs { ({ s with lead := m.From' } : NState) with logst := ls' }
          [appResp id { s with lead := m.From' } m.From' false lastnewi (W64 0) (W64 0)] ∧
        ls'.prev = s.logst.prev ∧ ls'.sents ++ ls'.uents = es' ∧
        ls'.committed = accCommit s.logst.committed m.Commit' lastnewi := by
      obtain ⟨pvs, h⟩ := ((hend (by rw [htr]; rfl)) hty).2.2.2 hns hnHup hnV
      rw [hpre pvs] at h
      obtain ⟨scfg, sv, d, c', hf⟩ := h.1 hrole
      unfold FollowerStepResultC at hf
      obtain ⟨-, hf⟩ := hf
      rw [hTy] at hf
      simp [MsgVoteResp, MsgProp, MsgApp] at hf
      obtain ⟨-, hf⟩ := hf
      unfold HandleAppResult at hf
      try simp only at hf
      rcases hf with ⟨h, -⟩ | ⟨-, ln2, es2, ls', h2, hp', hes2, -, hc2, -, -, h⟩ | ⟨-, hnm, -⟩
      · exact absurd h (by omega)
      · rw [show s.logst.prev = base0 from hbase] at h2
        have h3 := h2.symm.trans happ
        simp only [Option.some.injEq, Prod.mk.injEq] at h3
        obtain ⟨rfl, rfl⟩ := h3
        exact ⟨ls', h, hp', hes2, by rw [hc2]; rfl⟩
      · exact absurd hmt hnm
    subst hse
    unfold stepOut
    dsimp only [voteR]
    icases Hout with (⟨Hgh, Hc⟩ | ⟨Hgh, Hc⟩ | ⟨Hgh, Hc, -⟩ | %h | ⟨%b, %N, %h⟩)
    rotate_right 2
    · exact h.elim
    · exact h.elim
    all_goals
      icases ownStepGhost_nsLink γ md c id s $$ Hgh with ⟨%Hnl, Hgh⟩
      imod ownStepGhost_appAccFacts γ md c id s (absMsg .app m ents ctx) lastnewi es' rfl hterm hbase hge happ hfit
        $$ [$Hm $Hgh] with ⟨Hgh, -, %Hf⟩
      obtain ⟨hwr, hwr', hwN, hcl, hli, hreb, hBN⟩ := Hf
      have hre : γ.reTrace.isSome := by rw [← Hnl.2.1, htr]; rfl
      have hb61 : traceNumBound = 2 ^ 61 := rfl
      obtain ⟨hbN, -, hq, -, -⟩ := newLog_pure tn.voters (toPState s).log ents es' (uint.nat m.Index') m.LogTerm'
        lastnewi 0 hbL (hbN0 hreb) hwfZ (by word) hnw (Nat.zero_le _) happ'
      have hli' : uint.Z lastnewi = (uint.nat m.Index' : Int) + ents.length := by rw [hpZ]; exact hli
      have hlast : uint.Z lastnewi ≤ es'.length := by omega
      have hmono : ∀ C cs P, VPin tn.voters
          (toC (confAbs tn.voters) (doneSrv a0 (logAbs tn.voters tn.voters.length 1 es') (idAbs m.From')
            (min ma.commitIndex ((uint.nat m.Index' : Int) + ents.length))))
          (P0 ++ [doneResp a0 ma (uint.nat m.Index') ents.length]) C cs P →
          SimIdle C (sendMsgs { ({ s with lead := m.From' } : NState) with logst := ls' }
            [appResp id { s with lead := m.From' } m.From' false lastnewi (W64 0) (W64 0)]) cs P := by
        rintro C cs P ⟨rfl, rfl, rfl⟩
        have hP0' : P0 = pendAbs tn.voters s.outbox := hP0
        rw [hP0']
        exact accEnd_simIdle tn.voters id s m a0 ma ls' es' lastnewi (uint.nat m.Index') ents.length hR0 hs0 bt
          hrole hprev' hes' hcm' hbN hwN hBN hli' hlast hcp hmcm hmsub hmd hms
      iframe Hgh
      isplitl [Hc]
      · iapply trCapB_monoΛ (some γd) γ r id c true _ _ _ (fun o h => .inr h)
        iapply trCapB_mono (some γd) γ r id c true _ _ _ hmono $$ Hc
      · ipureintro
        intro _ x hx
        simp only [sendMsgs, List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact .inl hx
        · exact .inr (Msg.trOk_of_nums (by intro h; cases h) (by intro h; cases h)
            (fun _ => appResp_nums id _ m.From' lastnewi hT (by
              show uint.nat lastnewi < traceNumBound; have := uint_Z_nonneg lastnewi
              rw [hb61] at hBN ⊢; word)))

end paths

end EtcdGrove
end Perennial
