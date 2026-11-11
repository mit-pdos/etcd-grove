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

end fx

end EtcdGrove
end Perennial
