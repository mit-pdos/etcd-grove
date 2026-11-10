/-
Lean-first (no Rocq counterpart). **A receive line's phantom replies, discharged** (2026-11-10,
trace-check amendment A2, `notes/decisions.md`, "Amendment A2 (Q14)"): the sufficiency check of the
amendment. Since A2 a receive line's phantoms are a function `ph` of the receiving server
(`PhaseStepR`, `FxPresR`, `trCap_fire_recv.statement`), so the line's facts `FxPresR` can be proved
for them; before, they were arbitrary and `simFx` (`SpecInv`'s `TermsLe`, the messages' `msgFacts`)
was not provable of the bag they lead to (slice 15's finding, plan Q14).

- `recvPhantoms m a`: the phantoms of every receive line (pre-vote and check-quorum off): the
  specification's reply to a lower-term request (`phantomOf`, as `lineEffect_staleReq`'s effect),
  which raft ignores; none otherwise (raft's replies are the share's `P'`).
- `simFx_congr`: `simFx` reads the servers only up to `toC` (the share's view), and the bags only by
  their domains; `simFx_discard`, `simFx_send_plain`: consuming a message, and sending a message that
  carries no entries, grants nothing and is of its source's term at most (a phantom).
- `simFx_staleReqLine`: the step `FxPresR` asks of a lower-term request's line at `recvPhantoms m`,
  for one state: at phases that leave the share's server (up to `toC`) and list as they are (raft
  ignores the request), the facts after the line from those before **and the bags' responses
  canonical** (`RespCanon`), by which the uniqueness after the phantom holds (`msgsUniq_staleReq`).
  `simFx` (frozen) does not hold `RespCanon`, and the uniqueness after a send does not follow from it
  without (review a2-r1's F1/F2: a stray response differing from the phantom in a field no line reads):
  `FxPresR` itself, at this or any line that sends, waits on that clause (plan, Q15).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRecvGate

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts]

/-- **A receive line's phantom replies** at the receiving server `a` (pre-vote and check-quorum
off): the specification's refusal of a lower-term request (`phantomOf`), which raft ignores; none
for any other message (raft sends the specification's replies itself). -/
def recvPhantoms (m : Etcdraft.Msg) (a : Etcdraft.Server) : List Etcdraft.Msg :=
  if (m.type = .appendEntriesRequest ∨ m.type = .requestVoteRequest) ∧ m.term < a.currentTerm then
    [phantomOf a m]
  else []

theorem recvPhantoms_stale (m : Etcdraft.Msg) (a : Etcdraft.Server)
    (hty : m.type = .appendEntriesRequest ∨ m.type = .requestVoteRequest) (hlt : m.term < a.currentTerm) :
    recvPhantoms m a = [phantomOf a m] := by
  unfold recvPhantoms; rw [if_pos (show _ ∧ _ from ⟨hty, hlt⟩)]

/-- A phantom's fields: a refusal, no entries, of its source's (the receiver's) term. -/
theorem phantomOf_facts (a : Etcdraft.Server) (m : Etcdraft.Msg) :
    (phantomOf a m).entries = [] ∧ (phantomOf a m).type ≠ .appendEntriesRequest ∧
    ((phantomOf a m).type = .appendEntriesResponse → (phantomOf a m).success = false) ∧
    ((phantomOf a m).type = .requestVoteResponse → (phantomOf a m).voteGranted = false) ∧
    (phantomOf a m).term = a.currentTerm ∧ (phantomOf a m).source = m.dest := by
  unfold phantomOf
  split <;> simp

/-- **The bags' uniqueness reads only the bags' domains.** -/
theorem msgsUniq_mono {σ σ' : Etcdraft.State}
    (hsub : ∀ x ∈ σ'.messages.domain ++ σ'.pendingMessages.domain,
      x ∈ σ.messages.domain ++ σ.pendingMessages.domain) (h : MsgsUniq σ) : MsgsUniq σ' :=
  fun ln m1 m2 h1 h2 => h ln m1 m2 (hsub m1 h1) (hsub m2 h2)

/-- **`SpecInv` at states that agree on what it reads**, the match indices on the servers only (as
`toC` keeps them): `specInv_congr` with `hM` weakened. -/
theorem specInv_congr_srv {σ σ' : Etcdraft.State} (h : TraceSpecInv.SpecInv σ) (hsrv : σ'.server = σ.server)
    (hm : σ'.messages.domain = σ.messages.domain) (hp : σ'.pendingMessages.domain = σ.pendingMessages.domain)
    (hT : ∀ j, (σ'.s j).currentTerm = (σ.s j).currentTerm) (hS : ∀ j, (σ'.s j).state = (σ.s j).state)
    (hL : ∀ j, (σ'.s j).log = (σ.s j).log) (hD : ∀ j, (σ'.s j).durable = (σ.s j).durable)
    (hV : ∀ j, (σ'.s j).votesGranted = (σ.s j).votesGranted)
    (hC : ∀ j, (σ'.s j).commitIndex = (σ.s j).commitIndex)
    (hM : ∀ j, ∀ k ∈ σ.server, (σ'.s j).matchIndex k = (σ.s j).matchIndex k)
    (hG : ∀ j, (σ'.s j).config = (σ.s j).config) : TraceSpecInv.SpecInv σ' := by
  -- `σ'` with `σ`'s match indices first (`specInv_congr`), then only the match indices off the servers
  let σ'' : Etcdraft.State := { σ' with s := fun j => { σ'.s j with matchIndex := (σ.s j).matchIndex } }
  have h'' : TraceSpecInv.SpecInv σ'' :=
    TraceSpecInv.specInv_congr h hsrv hm hp hT hS hL hD hV hC (fun _ => rfl) hG
  obtain ⟨hLE, hDu, hTm, hCa, hP, hCW, hRC, hRCC, hLDP, hLT, hCF⟩ := h''
  refine ⟨hLE, ?_, hTm, hCa, hP, hCW, hRC, hRCC, hLDP, hLT, hCF⟩
  intro i hi hl
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hDu i hi hl
  refine ⟨a1, a2, ?_, a4, a5, a6, a7⟩
  intro k hk
  have := a3 k hk
  have hk' : k ∈ σ.server := by rw [← hsrv]; exact hk
  simp only [σ''] at this ⊢
  rw [hM i k hk']; exact this

/-! ### The bags' uniqueness after a phantom (review a2-r1's F1/F2, plan Q15)

`MsgsUniq` after a send does not follow from `simFx`: a receive line's `recvPred` ignores some fields of
a response (a refusal's `matchIndex`, a vote response's `lastLogIndex`/`lastLogTerm`, a response's
entries), so a bag may hold a response a line matches together with the phantom (review a2-r1's
counterexample). Raft's and the specification's responses are canonical in those fields;
`RespCanon` says so, and with it the uniqueness after a canonical response follows
(`msgsUniq_send_canon`). Not a clause of the frozen `simFx` (Q15). -/

/-- A response is **canonical** in the fields no receive line reads: a vote response (or pre-vote's)
has only its type, term, grant, source and destination; a refused append response only its type,
subtype, term, source and destination. -/
def RespCanonMsg (x : Etcdraft.Msg) : Prop :=
  ((x.type = .requestVoteResponse ∨ x.type = .preVoteResponse) →
    x = { type := x.type, term := x.term, voteGranted := x.voteGranted, source := x.source, dest := x.dest }) ∧
  (x.type = .appendEntriesResponse → x.success = false →
    x = { type := x.type, subtype := x.subtype, term := x.term, success := false, source := x.source,
          dest := x.dest })

/-- Every response in the bags canonical. -/
def RespCanon (σ : Etcdraft.State) : Prop := ∀ x ∈ σ.messages.domain ++ σ.pendingMessages.domain, RespCanonMsg x

theorem phantomOf_canon (a : Etcdraft.Server) (m : Etcdraft.Msg) : RespCanonMsg (phantomOf a m) := by
  unfold RespCanonMsg phantomOf
  split <;> simp

/-- **Two canonical messages a line matches, one of them a vote response or a refused append response,
are equal.** -/
theorem recvPred_canon_eq (ln : Etcdraft.Line) (y p : Etcdraft.Msg) (hyc : RespCanonMsg y)
    (hpc : RespCanonMsg p)
    (hpr : (p.type = .appendEntriesResponse ∧ p.success = false) ∨
      p.type = .requestVoteResponse ∨ p.type = .preVoteResponse)
    (hy : recvPred ln y = true) (hp : recvPred ln p = true) : y = p := by
  unfold recvPred at hy hp
  split at hy
  · rw [if_pos ‹_›] at hp
    unfold Etcdraft.Line.isAppendEntriesRequest at hp
    split at hp
    · cases hp
    · simp only [Bool.and_eq_true, beq_iff_eq] at hp
      rcases hpr with ⟨h, -⟩ | h | h <;> rw [hp.1.1.1.1.1.1.1.1] at h <;> cases h
  · rw [if_neg ‹_›] at hp
    split at hy
    · rw [if_pos ‹_›] at hp
      unfold Etcdraft.Line.isAppendEntriesResponse at hy hp
      split at hy
      · cases hy
      · rename_i ev hev
        rw [hev] at hp
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hy hp
        obtain ⟨⟨⟨⟨⟨⟨⟨y1, y2⟩, y3⟩, y4⟩, y5⟩, y6⟩, y7⟩, -⟩ := hy
        obtain ⟨⟨⟨⟨⟨⟨⟨p1, p2⟩, p3⟩, p4⟩, p5⟩, p6⟩, p7⟩, -⟩ := hp
        have hps : p.success = false := by
          rcases hpr with ⟨-, h⟩ | h | h
          · exact h
          · rw [p1] at h; cases h
          · rw [p1] at h; cases h
        have hys : y.success = false := by rw [y7, ← p7, hps]
        have hsub : y.subtype = p.subtype := by rw [y3] at p3; exact Option.some.inj p3
        rw [hyc.2 y1 hys, hpc.2 p1 hps]
        simp only [y1, p1, hsub, y5, p5, y4, p4, y6, p6]
    · rw [if_neg ‹_›] at hp
      split at hy
      · rw [if_pos ‹_›] at hp
        unfold Etcdraft.Line.isRequestVoteRequest at hp
        split at hp
        · cases hp
        · simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hp
          rcases hpr with ⟨h, -⟩ | h | h <;> rcases hp.1.1.1.1.1.1 with h' | h' <;> rw [h'] at h <;> cases h
      · rw [if_neg ‹_›] at hp
        unfold Etcdraft.Line.isRequestVoteResponse at hy hp
        split at hy
        · cases hy
        · rename_i ev hev
          rw [hev] at hp
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hy hp
          obtain ⟨⟨⟨⟨⟨y1, y2⟩, y3⟩, y4⟩, y5⟩, y6⟩ := hy
          obtain ⟨⟨⟨⟨⟨p1, p2⟩, p3⟩, p4⟩, p5⟩, p6⟩ := hp
          have hty : y.type = p.type := by rw [y2] at p2; exact Option.some.inj p2
          rw [hyc.1 y1, hpc.1 p1]
          simp only [hty, y3, p3, y4, p4, y5, p5, y6, p6]

/-- **The uniqueness after sending a canonical response** (a phantom), with every response in the
bags canonical. -/
theorem msgsUniq_send_canon (σ : Etcdraft.State) (p : Etcdraft.Msg) (hu : MsgsUniq σ) (hc : RespCanon σ)
    (hpc : RespCanonMsg p)
    (hpr : (p.type = .appendEntriesResponse ∧ p.success = false) ∨
      p.type = .requestVoteResponse ∨ p.type = .preVoteResponse) :
    MsgsUniq (σ.send p) := by
  intro ln m1 m2 h1 h2 r1 r2
  rcases TraceSpecInv.mem_msgs_send σ p m1 h1 with g1 | e1 <;>
    rcases TraceSpecInv.mem_msgs_send σ p m2 h2 with g2 | e2
  · exact hu ln m1 m2 g1 g2 r1 r2
  · subst e2; exact recvPred_canon_eq ln m1 m2 (hc m1 g1) hpc hpr r1 r2
  · subst e1; exact (recvPred_canon_eq ln m2 m1 (hc m2 g2) hpc hpr r2 r1).symm
  · rw [e1, e2]

/-- The phantom is a vote response or a refused append response. -/
theorem phantomOf_resp (a : Etcdraft.Server) (m : Etcdraft.Msg) :
    ((phantomOf a m).type = .appendEntriesResponse ∧ (phantomOf a m).success = false) ∨
      (phantomOf a m).type = .requestVoteResponse ∨ (phantomOf a m).type = .preVoteResponse := by
  unfold phantomOf; split <;> simp

/-- **The uniqueness after a lower-term request's line**, from the uniqueness and the canonical
responses before it. -/
theorem msgsUniq_staleReq (σ : Etcdraft.State) (m : Etcdraft.Msg) (srv : Etcdraft.Server)
    (hu : MsgsUniq σ) (hc : RespCanon σ) :
    MsgsUniq ((σ.discard m).send (phantomOf srv m)) := by
  have hsub : ∀ x ∈ (σ.discard m).messages.domain ++ (σ.discard m).pendingMessages.domain,
      x ∈ σ.messages.domain ++ σ.pendingMessages.domain := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (TraceSpecInv.mem_without _ _ _ hx)
    · exact List.mem_append_right _ hx
  exact msgsUniq_send_canon _ _ (msgsUniq_mono hsub hu) (fun x hx => hc x (hsub x hx))
    (phantomOf_canon srv m) (phantomOf_resp srv m)

end pure

section facts
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Every voter's facts read only the servers. -/
theorem allFacts_congr_s (γ : RaftNames) (C : List w64) (σ σ' : Etcdraft.State) (h : σ'.s = σ.s) :
    allFacts (GF := GF) γ C σ ⊢ allFacts γ C σ' := by
  unfold allFacts; rw [h]

/-- A voter's facts read its server's log, commit index, term and role only. -/
theorem srvFacts_congr (γ : RaftNames) (C : List w64) (j : w64) (v w : Etcdraft.Server)
    (hl : w.log = v.log) (hc : w.commitIndex = v.commitIndex) (ht : w.currentTerm = v.currentTerm)
    (hs : w.state = v.state) :
    srvFacts (GF := GF) γ C j v ⊢ srvFacts γ C j w := by
  unfold srvFacts
  simp only [hl, hc, ht, hs]
  exact .rfl

/-- **`simFx` reads the servers up to `toC`** (at the state's servers) and the bags by their domains. -/
theorem simFx_congr (γ : RaftNames) (C : List w64) (σ σ' : Etcdraft.State) (hsrv : σ'.server = σ.server)
    (hm : σ'.messages.domain = σ.messages.domain) (hp : σ'.pendingMessages.domain = σ.pendingMessages.domain)
    (hs : ∀ j, toC σ.server (σ'.s j) = toC σ.server (σ.s j)) :
    simFx (GF := GF) γ C σ ⊢ simFx γ C σ' := by
  have hT : ∀ j, (σ'.s j).currentTerm = (σ.s j).currentTerm := fun j => congrArg ServerC.currentTerm (hs j)
  have hS : ∀ j, (σ'.s j).state = (σ.s j).state := fun j => congrArg ServerC.state (hs j)
  have hL : ∀ j, (σ'.s j).log = (σ.s j).log := fun j => congrArg ServerC.log (hs j)
  have hD : ∀ j, (σ'.s j).durable = (σ.s j).durable := fun j => congrArg ServerC.durable (hs j)
  have hV : ∀ j, (σ'.s j).votesGranted = (σ.s j).votesGranted := fun j => congrArg ServerC.votesGranted (hs j)
  have hC : ∀ j, (σ'.s j).commitIndex = (σ.s j).commitIndex := fun j => congrArg ServerC.commitIndex (hs j)
  have hG : ∀ j, (σ'.s j).config = (σ.s j).config := fun j => congrArg ServerC.config (hs j)
  have hM : ∀ j, ∀ k ∈ σ.server, (σ'.s j).matchIndex k = (σ.s j).matchIndex k :=
    fun j => List.map_inj_left.1 (congrArg ServerC.matchIndex (hs j))
  iintro Hfx
  iunfold simFx at Hfx
  iunfold simFx
  icases Hfx with ⟨#Hal, #Hmf, %Hp⟩
  obtain ⟨hsi, hq, hu⟩ := Hp
  isplitl
  · iunfold allFacts at Hal
    iunfold allFacts
    imodintro
    iintro %j %hj
    iapply srvFacts_congr γ C j _ _ (hL _) (hC _) (hT _) (hS _)
    iapply Hal $$ %j %hj
  isplitl
  · imodintro
    iintro %x %hx
    iapply Hmf
    ipureintro
    rw [hm, hp] at hx; exact hx
  ipureintro
  refine ⟨specInv_congr_srv hsi hsrv hm hp hT hS hL hD hV hC hM hG,
    quorumLogF_congr σ σ' hsrv hL hC hG hq, msgsUniq_mono (fun x hx => by rw [hm, hp] at hx; exact hx) hu⟩

/-- **Consuming a message keeps the facts.** -/
theorem simFx_discard (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) (m : Etcdraft.Msg) :
    simFx (GF := GF) γ C σ ⊢ simFx γ C (σ.discard m) := by
  have hsub : ∀ x ∈ (σ.discard m).messages.domain ++ (σ.discard m).pendingMessages.domain,
      x ∈ σ.messages.domain ++ σ.pendingMessages.domain := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact List.mem_append_left _ (TraceSpecInv.mem_without _ _ _ hx)
    · exact List.mem_append_right _ hx
  iintro Hfx
  iunfold simFx at Hfx
  iunfold simFx
  icases Hfx with ⟨#Hal, #Hmf, %Hp⟩
  obtain ⟨hsi, hq, hu⟩ := Hp
  isplitl
  · iapply allFacts_congr_s γ C σ (σ.discard m) rfl
    iexact Hal
  isplitl
  · imodintro
    iintro %x %hx
    iapply Hmf
    ipureintro; exact hsub x hx
  ipureintro
  exact ⟨TraceSpecInv.specInv_discard m hsi, hq, msgsUniq_mono hsub hu⟩

/-- **Sending a plain message keeps the facts** (no entries, not an append request, a refusal, of its
source's term at most: a phantom), given the bags' uniqueness after it. -/
theorem simFx_send_plain (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) (x : Etcdraft.Msg)
    (he : x.entries = []) (hq : x.type ≠ .appendEntriesRequest)
    (hs : x.type = .appendEntriesResponse → x.success = false)
    (hv : x.type = .requestVoteResponse → x.voteGranted = false)
    (ht : x.term ≤ (σ.s x.source).currentTerm) (hu : MsgsUniq (σ.send x)) :
    simFx (GF := GF) γ C σ ⊢ simFx γ C (σ.send x) := by
  iintro Hfx
  iunfold simFx at Hfx
  iunfold simFx
  icases Hfx with ⟨#Hal, #Hmf, %Hp⟩
  obtain ⟨hsi, hql, -⟩ := Hp
  isplitl
  · iapply allFacts_congr_s γ C σ (σ.send x) rfl
    iexact Hal
  isplitl
  · imodintro
    iintro %y %hy
    rcases TraceSpecInv.mem_msgs_send σ x y hy with hy | rfl
    · iapply Hmf; ipureintro; exact hy
    · unfold msgFacts; rw [if_neg hq]; ipureintro; exact he
  ipureintro
  exact ⟨TraceSpecInv.specInv_send hsi (TraceSpecInv.msgOk_plain σ x he hq hs hv ht), hql, hu⟩

/-- **The facts across a lower-term request's receive line** (`FxPresR`'s step at the phantoms
`recvPhantoms m`, for one state `σ`): raft ignores the request, so the line's phases keep the share's
server (`toC a' = toC a`) and list (`P' = []`), and the specification answers it with the phantom
refusal. From the facts before and the responses in the bags canonical (`hc`), the facts hold at the
line's result. `FxPresR` itself (all states with the facts) needs `RespCanon` among the facts
(`simFx`, frozen: plan Q15); review a2-r1's F1: the uniqueness after the phantom does not follow from
`simFx` alone. -/
theorem simFx_staleReqLine (γ : RaftNames) (id : w64) (C : List w64) (m : Etcdraft.Msg)
    (σ : Etcdraft.State) (a a' : Etcdraft.Server)
    (hty : m.type = .appendEntriesRequest ∨ m.type = .requestVoteRequest) (hdst : m.dest = idAbs id)
    (hlt : m.term < a.currentTerm) (hsrv : σ.server = confAbs C) (hσa : σ.s (idAbs id) = a)
    (ha' : toC (confAbs C) a' = toC (confAbs C) a) (hc : RespCanon σ) :
    simFx (GF := GF) γ C σ ⊢
      simFx γ C (withNode σ (idAbs id) a' (fun b => b.without m)
        (fun b => ([] ++ recvPhantoms m a).foldl Etcdraft.Bag.with b)) := by
  iintro #Hfx
  have hph : recvPhantoms m a = [phantomOf a m] := recvPhantoms_stale m a hty hlt
  obtain ⟨phe, phq, phs, phv, pht, phsrc⟩ := phantomOf_facts a m
  -- the bags' uniqueness before the line, then after the phantom
  ihave #Hfx0 := Hfx
  iunfold simFx at Hfx0
  icases Hfx0 with ⟨-, -, %Hp0⟩
  have hu1 := msgsUniq_staleReq σ m a Hp0.2.2 hc
  -- the request consumed, the phantom sent, then the line's result (the same up to `toC`)
  ihave #H1 := simFx_discard γ C σ m $$ Hfx
  ihave #H2 := simFx_send_plain γ C (σ.discard m) (phantomOf a m) phe phq phs phv
    (by rw [pht, phsrc, hdst]; show a.currentTerm ≤ (σ.s (idAbs id)).currentTerm; rw [hσa]; exact Int.le_refl _) hu1 $$ H1
  have hs : ∀ j, toC ((σ.discard m).send (phantomOf a m)).server
      ((withNode σ (idAbs id) a' (fun b => b.without m)
        (fun b => ([] ++ recvPhantoms m a).foldl Etcdraft.Bag.with b)).s j) =
      toC ((σ.discard m).send (phantomOf a m)).server (((σ.discard m).send (phantomOf a m)).s j) := by
    intro j
    show toC σ.server (if j = idAbs id then a' else σ.s j) = toC σ.server (σ.s j)
    split
    · rename_i hj; subst hj; rw [hσa, hsrv, ha']
    · rfl
  ihave #H3 := simFx_congr γ C ((σ.discard m).send (phantomOf a m))
    (withNode σ (idAbs id) a' (fun b => b.without m) (fun b => ([] ++ recvPhantoms m a).foldl Etcdraft.Bag.with b))
    rfl rfl (by rw [hph]; rfl) hs $$ H2
  iexact H3

end facts

end EtcdGrove
end Perennial
