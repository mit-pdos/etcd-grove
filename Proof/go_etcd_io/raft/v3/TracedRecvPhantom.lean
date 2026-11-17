/-
Lean-first (no Rocq counterpart). **Amendment A2's sufficiency checks** (2026-11-10, trace-check
amendment A2, `notes/decisions.md`, "Amendment A2 (Q14, Q15, Q16)"): a receive line's facts `FxPresR` at
its phantoms (Q14: the phantoms a function `ph` of the receiving server) and a send line's facts
`FxPres` (Q15: `simFx`'s shape clause `MsgsShape`, every message in flight canonical), each proved for
one line. Before A2 neither was provable: the phantoms were arbitrary (slice 15), and a message in
flight differing from a new one only in a field no line logs broke `MsgsUniq` (review a2-r1, slice 16).

- `recvPhantoms m a`: the phantoms of every receive line (pre-vote and check-quorum off): the
  specification's reply to a lower-term request (`phantomOf`, as `lineEffect_staleReq`'s effect),
  which raft ignores; none otherwise (raft's replies are the share's `P'`).
- `recvPred_canon_eq`, `msgsUniq_send_canon`: two canonical messages one line matches are equal (but
  for an append request's entries); the uniqueness and the shape after sending a canonical message.
- `simFx_congr` (`simFx` reads the servers only up to `toC`, the bags by their domains),
  `simFx_discard`, `simFx_send` (a message fine to send, `MsgOk`, with its `msgFacts`, canonical).
- (Q16) `PinnedBy`, `AppSliceOf`, `pinned_of_slices`: a leader's new `"app"` request, a slice of its
  log, pins every in-flight message (`AppSlices`), so its line keeps `MsgsUniq`.
- `fxPresR_staleReq`: `FxPresR` of a lower-term request's receive line at `recvPhantoms m`;
  `fxPres_heartbeat`: `FxPres` of a heartbeat's send line (`msgOk_heartbeat`); `fxPres_app`: of an
  `"app"` send line with entries (`msgOk_app`); each at phases that keep the share's server (up to
  `toC`) and add the line's message to its list (none for the stale line).
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

/-- (Amendment A6, Q23) A phantom reply goes back to its request's source. -/
theorem phantomOf_dest (a : Etcdraft.Server) (m : Etcdraft.Msg) : (phantomOf a m).dest = m.source := by
  unfold phantomOf
  split <;> rfl

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


/-! ### The bags' uniqueness after a new canonical message (amendment A2, Q15)

A receive line's `recvPred` reads only some fields of a message; `simFx`'s `MsgsShape` (every message in
flight canonical, `canonMsg`) fixes the others, so two canonical messages one line matches are equal,
but for an append request's entries' contents (not a heartbeat's: it has none). -/

theorem canonMsg_type (x : Etcdraft.Msg) : (canonMsg x).type = x.type := by
  unfold canonMsg; split <;> (try split) <;> rfl

/-- An append request whose content a line pins: a heartbeat, or an `"app"` request with no entries
(review a2-r4's S2); any other message. -/
def ContentLogged (p : Etcdraft.Msg) : Prop :=
  p.type = .appendEntriesRequest → p.subtype = "heartbeat" ∨ (p.subtype = "app" ∧ p.entries = [])

/-- **`y` agrees with `p` where no line looks** (amendment A2, Q16): `p` not an append request, or a
heartbeat, or an `"app"` request whose entries `y` carries too whenever it is from the same sender, of
the same term, after the same entry, with as many entries (what `AppSlices` gives for a leader's
requests of its term). -/
def PinnedBy (y p : Etcdraft.Msg) : Prop :=
  p.type = .appendEntriesRequest → p.subtype = "heartbeat" ∨
    (p.subtype = "app" ∧ (y.type = .appendEntriesRequest → y.source = p.source → y.term = p.term →
      y.prevLogIndex = p.prevLogIndex → y.entries.length = p.entries.length → y.entries = p.entries))

theorem ContentLogged.pinned {p : Etcdraft.Msg} (h : ContentLogged p) (y : Etcdraft.Msg) : PinnedBy y p := by
  intro hp
  rcases h hp with h | ⟨h1, h2⟩
  · exact .inl h
  · refine .inr ⟨h1, fun _ _ _ _ hl => ?_⟩
    rw [h2] at hl ⊢; exact List.eq_nil_of_length_eq_zero hl

/-- **Two canonical messages a line matches are equal**, the first pinned by the second where the line
does not look (`PinnedBy`: not a snapshot, and an `"app"` request's entries agreeing). -/
theorem recvPred_canon_eq (ln : Etcdraft.Line) (y p : Etcdraft.Msg) (hy0 : canonMsg y = y)
    (hp0 : canonMsg p = p) (hpk : PinnedBy y p)
    (hy : recvPred ln y = true) (hp : recvPred ln p = true) : y = p := by
  unfold recvPred at hy hp
  split at hy
  · rw [if_pos ‹_›] at hp
    unfold Etcdraft.Line.isAppendEntriesRequest at hy hp
    split at hy
    · cases hy
    · rename_i ev hev
      rw [hev] at hp
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hy hp
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨y1, y2⟩, y3⟩, y4⟩, y5⟩, y6⟩, y7⟩, y8⟩, y9⟩ := hy
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨p1, p2⟩, p3⟩, p4⟩, p5⟩, p6⟩, p7⟩, p8⟩, p9⟩ := hp
      have hsub : y.subtype = p.subtype := by rw [y3] at p3; exact Option.some.inj p3
      rcases hpk p1 with hps | ⟨hps, hent⟩
      · have hys : y.subtype = "heartbeat" := by rw [hsub, hps]
        have hc : y.commitIndex = p.commitIndex := by
          rcases y7 with h | h
          · rw [hys] at h; exact absurd h (by decide)
          rcases p7 with h' | h'
          · rw [hps] at h'; exact absurd h' (by decide)
          rw [h, h']
        rw [← hy0, ← hp0]
        unfold canonMsg
        rw [y1, p1]
        simp only [if_pos hps, hsub, y4, p4, y5, p5, y6, p6, hc]
      · have hys : y.subtype = "app" := by rw [hsub, hps]
        have hc : y.commitIndex = p.commitIndex := by
          rcases y7 with h | h
          · rw [hys] at h; exact absurd h (by decide)
          rcases p7 with h' | h'
          · rw [hps] at h'; exact absurd h' (by decide)
          rw [h, h']
        have hpl : y.prevLogTerm = p.prevLogTerm ∧ y.prevLogIndex = p.prevLogIndex := by
          rcases y8 with h | h
          · rw [hys] at h; exact absurd h (by decide)
          rcases p8 with h' | h'
          · rw [hps] at h'; exact absurd h' (by decide)
          exact ⟨by rw [h.1, h'.1], by rw [h.2, h'.2]⟩
        have hlen : y.entries.length = p.entries.length := by
          have : (y.entries.length : Int) = p.entries.length := by rw [y9, p9]
          exact_mod_cast this
        have hye : y.entries = p.entries := hent y1 (by rw [y5, p5]) (by rw [y6, p6]) hpl.2 hlen
        rw [← hy0, ← hp0]
        unfold canonMsg
        rw [y1, p1]
        simp only [hsub, hps, y4, p4, y5, p5, y6, p6, hc, hpl.1, hpl.2, hye]
  · rw [if_neg ‹_›] at hp
    split at hy
    · rw [if_pos ‹_›] at hp
      unfold Etcdraft.Line.isAppendEntriesResponse at hy hp
      split at hy
      · cases hy
      · rename_i ev hev
        rw [hev] at hp
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hy hp
        obtain ⟨⟨⟨⟨⟨⟨⟨y1, y2⟩, y3⟩, y4⟩, y5⟩, y6⟩, y7⟩, y8⟩ := hy
        obtain ⟨⟨⟨⟨⟨⟨⟨p1, p2⟩, p3⟩, p4⟩, p5⟩, p6⟩, p7⟩, p8⟩ := hp
        have hsub : y.subtype = p.subtype := by rw [y3] at p3; exact Option.some.inj p3
        have hsu : y.success = p.success := by rw [y7, p7]
        have hmi : (if y.success && y.subtype != "heartbeat" then y.matchIndex else 0) =
            (if p.success && p.subtype != "heartbeat" then p.matchIndex else 0) := by
          rw [hsub, hsu]
          by_cases hh : (p.success && p.subtype != "heartbeat") = true
          · rw [if_pos hh, if_pos hh]
            simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hh
            have hr : ev.reject = false := by
              have := hh.1; rw [p7] at this; simpa using this
            rcases y8 with (h | h) | h
            · rw [hr] at h; cases h
            · rw [hsub] at h; exact absurd h hh.2
            rcases p8 with (h' | h') | h'
            · rw [hr] at h'; cases h'
            · exact absurd h' hh.2
            rw [h, h']
          · rw [if_neg hh, if_neg hh]
        rw [← hy0, ← hp0]
        unfold canonMsg
        rw [y1, p1]
        simp only at hmi ⊢
        rw [hmi, hsub, hsu, y4, p4, y5, p5, y6, p6]
    · rw [if_neg ‹_›] at hp
      split at hy
      · rw [if_pos ‹_›] at hp
        unfold Etcdraft.Line.isRequestVoteRequest at hy hp
        split at hy
        · cases hy
        · rename_i ev hev
          rw [hev] at hp
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hy hp
          obtain ⟨⟨⟨⟨⟨⟨y1, y2⟩, y3⟩, y4⟩, y5⟩, y6⟩, y7⟩ := hy
          obtain ⟨⟨⟨⟨⟨⟨p1, p2⟩, p3⟩, p4⟩, p5⟩, p6⟩, p7⟩ := hp
          have hty : y.type = p.type := by rw [y2] at p2; exact Option.some.inj p2
          rw [← hy0, ← hp0]
          unfold canonMsg
          rw [hty]
          rcases p1 with h | h <;> rw [h] <;> simp only [y3, p3, y4, p4, y5, p5, y6, p6, y7, p7]
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
          have hvg : y.voteGranted = p.voteGranted := by rw [y6, p6]
          rw [← hy0, ← hp0]
          unfold canonMsg
          rw [hty]
          rcases p1 with h | h <;> rw [h] <;> simp only [y3, p3, y4, p4, y5, p5, hvg]

/-- **The uniqueness and the shape after sending a canonical message `p` that pins every in-flight
message** (`PinnedBy`). -/
theorem msgsUniq_send_canon (σ : Etcdraft.State) (p : Etcdraft.Msg) (hu : MsgsUniq σ) (hc : MsgsShape σ)
    (hp0 : canonMsg p = p) (hpe : MsgEnds σ p) (hpk : ∀ y ∈ σ.messages.domain ++ σ.pendingMessages.domain, PinnedBy y p) :
    MsgsUniq (σ.send p) ∧ MsgsShape (σ.send p) := by
  constructor
  · intro ln m1 m2 h1 h2 r1 r2
    rcases TraceSpecInv.mem_msgs_send σ p m1 h1 with g1 | e1 <;>
      rcases TraceSpecInv.mem_msgs_send σ p m2 h2 with g2 | e2
    · exact hu ln m1 m2 g1 g2 r1 r2
    · subst e2; exact recvPred_canon_eq ln m1 m2 (hc.1 m1 g1).1 hp0 (hpk m1 g1) r1 r2
    · subst e1; exact (recvPred_canon_eq ln m2 m1 (hc.1 m2 g2).1 hp0 (hpk m2 g2) r2 r1).symm
    · rw [e1, e2]
  · refine ⟨fun x hx => ?_, hc.2⟩
    rcases TraceSpecInv.mem_msgs_send σ p x hx with g | e
    · exact hc.1 x g
    · rw [e]; exact ⟨hp0, hpe⟩

/-- `AppSlices`' clause for one message. -/
def AppSliceOf (σ : Etcdraft.State) (m : Etcdraft.Msg) : Prop :=
  m.type = .appendEntriesRequest →
    ∀ i ∈ σ.server, (σ.s i).state = Etcdraft.leader → (σ.s i).currentTerm = m.term → m.source = i →
      ∀ (k : Nat) (e : Etcdraft.Entry), m.entries[k]? = some e → (σ.s i).log[m.prevLogIndex.toNat + k]? = some e

theorem appSlices_iff (σ : Etcdraft.State) :
    AppSlices σ ↔ ∀ m ∈ σ.messages.domain ++ σ.pendingMessages.domain, AppSliceOf σ m := Iff.rfl

/-- A message with no entries has its clause. -/
theorem appSliceOf_nil (σ : Etcdraft.State) (m : Etcdraft.Msg) (h : m.entries = []) : AppSliceOf σ m := by
  intro _ _ _ _ _ _ k e he; rw [h] at he; simp at he

/-- **Sending keeps `AppSlices`** when the new message has its clause. -/
theorem appSlices_send (σ : Etcdraft.State) (x : Etcdraft.Msg) (h : AppSlices σ) (hx : AppSliceOf σ x) :
    AppSlices (σ.send x) := by
  intro m hm
  rcases TraceSpecInv.mem_msgs_send σ x m hm with g | e
  · exact h m g
  · rw [e]; exact hx

/-- **A leader's new `"app"` request, a slice of its log, pins every in-flight message** (`AppSlices`:
an in-flight request of the leader's term from it is a slice of the same log). -/
theorem pinned_of_slices (σ : Etcdraft.State) (p : Etcdraft.Msg) (i : Etcdraft.ID) (hi : i ∈ σ.server)
    (hl : (σ.s i).state = Etcdraft.leader) (ht : (σ.s i).currentTerm = p.term) (hsrc : p.source = i)
    (hps : p.subtype = "app")
    (hsl : ∀ (k : Nat) (e : Etcdraft.Entry), p.entries[k]? = some e → (σ.s i).log[p.prevLogIndex.toNat + k]? = some e)
    (has : AppSlices σ) : ∀ y ∈ σ.messages.domain ++ σ.pendingMessages.domain, PinnedBy y p := by
  intro y hy _
  refine .inr ⟨hps, fun hyt hys hyterm hypl hlen => ?_⟩
  have hy' := has y hy hyt i hi hl (by rw [ht, hyterm]) (by rw [hys, hsrc])
  apply List.ext_getElem?
  intro k
  by_cases hk : k < y.entries.length
  · have hk' : k < p.entries.length := hlen ▸ hk
    have e1 := hy' k _ (List.getElem?_eq_getElem hk)
    have e2 := hsl k _ (List.getElem?_eq_getElem hk')
    rw [hypl, e2] at e1
    rw [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk']
    exact e1.symm
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- **Raft's messages are canonical** (as the specification's, `msgAbs`): what a send line's facts need
of its message for `MsgsShape` (review a2-r3's F3). -/
theorem msgAbs_canon (C : List w64) (bl : Nat) (m : Msg) (ma : Etcdraft.Msg)
    (h : TraceSim.msgAbs C bl m = some ma) : canonMsg ma = ma := by
  unfold TraceSim.msgAbs at h
  cases hty : m.ty <;> simp only [hty] at h <;> cases h <;> simp [canonMsg] <;>
    (try split <;> simp_all) <;> (try (intro h1 h2; rw [h1] at h2; cases h2))

theorem phantomOf_canon (a : Etcdraft.Server) (m : Etcdraft.Msg) : canonMsg (phantomOf a m) = phantomOf a m := by
  unfold phantomOf
  split <;> simp [canonMsg]

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
  have hsub : ∀ x ∈ σ'.messages.domain ++ σ'.pendingMessages.domain,
      x ∈ σ.messages.domain ++ σ.pendingMessages.domain := fun x hx => by rw [hm, hp] at hx; exact hx
  iintro Hfx
  iunfold simFx at Hfx
  iunfold simFx
  icases Hfx with ⟨#Hal, #Hmf, #Hq, %Hp⟩
  obtain ⟨hsi, hu, hsh, has⟩ := Hp
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
    exact hsub x hx
  isplitl
  · iapply quorumLogF_congr γ C σ σ' hsrv hL hC (fun k => by rw [hT]; exact Int.le_refl _)
      (fun x hx _ => hsub x hx)
      (fun i hi => by rw [hS] at hi; exact ⟨hi, hT i, hM i⟩) $$ Hq
  ipureintro
  refine ⟨specInv_congr_srv hsi hsrv hm hp hT hS hL hD hV hC hM hG,
    msgsUniq_mono hsub hu,
    msgsShape_of hsrv hsub (fun j => congrArg ServerC.votesResponded (hs j)) hsh, ?_⟩
  intro m hm hty i hi hl ht hs k e he
  rw [hL]
  rw [hsrv] at hi; rw [hS] at hl; rw [hT] at ht
  exact has m (hsub m hm) hty i hi hl ht hs k e he

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
  icases Hfx with ⟨#Hal, #Hmf, #Hq, %Hp⟩
  obtain ⟨hsi, hu, hsh, has⟩ := Hp
  isplitl
  · iapply allFacts_congr_s γ C σ (σ.discard m) rfl
    iexact Hal
  isplitl
  · imodintro
    iintro %x %hx
    iapply Hmf
    ipureintro; exact hsub x hx
  isplitl
  · iapply quorumLogF_congr γ C σ (σ.discard m) rfl (fun _ => rfl) (fun _ => rfl) (fun _ => Int.le_refl _)
      (fun x hx _ => hsub x hx) (fun _ hi => ⟨hi, rfl, fun _ _ => rfl⟩) $$ Hq
  ipureintro
  exact ⟨TraceSpecInv.specInv_discard m hsi, msgsUniq_mono hsub hu, msgsShape_of (σ := σ) rfl hsub (fun _ => rfl) hsh,
    fun x hx => has x (hsub x hx)⟩

/-- **Sending a message keeps the facts** when it is fine to send (`MsgOk`), has its facts (`msgFacts`),
is canonical, pins every in-flight message (`PinnedBy`) and, an append request, is a slice of its
leading sender's log (`AppSliceOf`). -/
theorem simFx_send (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) (x : Etcdraft.Msg)
    (hok : TraceSpecInv.MsgOk σ x) (hx0 : canonMsg x = x)
    (hxk : ∀ y ∈ σ.messages.domain ++ σ.pendingMessages.domain, PinnedBy y x)
    (hxs : AppSliceOf σ x) (hxa : ¬ AckMsg x) (hxe : MsgEnds σ x) :
    (simFx (GF := GF) γ C σ ∗ msgFacts γ C x) ⊢ simFx γ C (σ.send x) := by
  iintro ⟨Hfx, #Hx⟩
  iunfold simFx at Hfx
  iunfold simFx
  icases Hfx with ⟨#Hal, #Hmf, #Hq, %Hp⟩
  obtain ⟨hsi, hu, hsh, has⟩ := Hp
  isplitl
  · iapply allFacts_congr_s γ C σ (σ.send x) rfl
    iexact Hal
  isplitl
  · imodintro
    iintro %y %hy
    rcases TraceSpecInv.mem_msgs_send σ x y hy with hy | rfl
    · iapply Hmf; ipureintro; exact hy
    · iexact Hx
  isplitl
  · iapply quorumLogF_congr γ C σ (σ.send x) rfl (fun _ => rfl) (fun _ => rfl) (fun _ => Int.le_refl _)
      (fun y hy hya => by
        rcases TraceSpecInv.mem_msgs_send σ x y hy with hy | rfl
        · exact hy
        · exact absurd hya hxa)
      (fun _ hi => ⟨hi, rfl, fun _ _ => rfl⟩) $$ Hq
  ipureintro
  obtain ⟨hu', hsh'⟩ := msgsUniq_send_canon σ x hu hsh hx0 hxe hxk
  exact ⟨TraceSpecInv.specInv_send hsi hok, hu', hsh', appSlices_send σ x has hxs⟩

/-- A message that is not an append request has the facts `⌜entries = []⌝`. -/
theorem msgFacts_plain (γ : RaftNames) (C : List w64) (x : Etcdraft.Msg) (hq : x.type ≠ .appendEntriesRequest)
    (he : x.entries = []) : ⊢ msgFacts (GF := GF) γ C x := by
  unfold msgFacts; rw [if_neg hq]; ipureintro; exact he

/-- **The facts of a lower-term request's receive line** (`FxPresR` at the phantoms `recvPhantoms m`):
raft ignores the request, so the line's phases keep the share's server and list (`hΦ'`), and the
specification answers it with the phantom refusal (`phantomOf`, canonical). The line has no
intermediate state (`Mid` empty). -/
theorem fxPresR_staleReq (γ : RaftNames) (id : w64) (m : Etcdraft.Msg) (E : TraceEv → Prop)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop)
    (hty : m.type = .appendEntriesRequest ∨ m.type = .requestVoteRequest) (hdst : m.dest = idAbs id)
    (hlt : ∀ C cs P, Φ C cs P → m.term < cs.currentTerm)
    (hΦ' : ∀ C cs P cs' P', Φ C cs P → Φ' C cs' (P ++ P') → cs' = cs ∧ P' = []) :
    ⊢ FxPresR (GF := GF) γ id m E (fun _ => False) (recvPhantoms m) Φ Φ' := by
  iunfold FxPresR
  imodintro
  iintro %C %cs %P %e %a %a' %P' %σ %hpre Htbl #Hfx
  obtain ⟨hΦ, -, hcs, hΦ1, -, hsrv, hσa, -, -, -, hmem⟩ := hpre
  obtain ⟨hcs', hP'⟩ := hΦ' C cs P _ P' hΦ hΦ1
  subst hP'
  have hph : recvPhantoms m a = [phantomOf a m] :=
    recvPhantoms_stale m a hty (by
      have h1 := hlt C cs P hΦ
      have h2 : (toC (confAbs C) a).currentTerm = a.currentTerm := rfl
      rw [hcs] at h2; rw [← h2]; exact h1)
  obtain ⟨phe, phq, phs, phv, pht, phsrc⟩ := phantomOf_facts a m
  -- (amendment A6, Q23) the phantom's ends, the request's reversed
  ihave %hme : ⌜MsgEnds σ m⌝ $$ []
  · ihave #Hf2 := Hfx
    iunfold simFx at Hf2
    icases Hf2 with ⟨-, -, -, %Hp2⟩
    ipureintro; exact (Hp2.2.2.1.1 m (List.mem_append_left _ hmem)).2
  -- the request consumed, the phantom sent, then the line's result (the same up to `toC`)
  ihave #H1 := simFx_discard γ C σ m $$ Hfx
  ihave #Hpf := msgFacts_plain (GF := GF) γ C (phantomOf a m) phq phe
  ihave #H2 := simFx_send γ C (σ.discard m) (phantomOf a m)
    (TraceSpecInv.msgOk_plain _ _ phe phq phs phv
      (by rw [pht, phsrc, hdst]; show a.currentTerm ≤ (σ.s (idAbs id)).currentTerm; rw [hσa]; exact Int.le_refl _))
    (phantomOf_canon a m) (fun y _ => ContentLogged.pinned (fun h => absurd h phq) y)
    (appSliceOf_nil _ _ phe) (fun h => by have := phs h.1; rw [h.2.1] at this; cases this)
    ⟨by rw [phsrc]; exact hme.2, by rw [phantomOf_dest]; exact hme.1⟩ $$ [$H1 $Hpf]
  have hs : ∀ j, toC ((σ.discard m).send (phantomOf a m)).server
      ((withNode σ (idAbs id) a' (fun b => b.without m)
        (fun b => ([] ++ recvPhantoms m a).foldl Etcdraft.Bag.with b)).s j) =
      toC ((σ.discard m).send (phantomOf a m)).server (((σ.discard m).send (phantomOf a m)).s j) := by
    intro j
    show toC σ.server (if j = idAbs id then a' else σ.s j) = toC σ.server (σ.s j)
    split
    · rename_i hj; subst hj; rw [hσa, hsrv, hcs', hcs]
    · rfl
  ihave #H3 := simFx_congr γ C ((σ.discard m).send (phantomOf a m))
    (withNode σ (idAbs id) a' (fun b => b.without m) (fun b => ([] ++ recvPhantoms m a).foldl Etcdraft.Bag.with b))
    rfl rfl (by rw [hph]; rfl) hs $$ H2
  iframe Htbl
  isplitl
  · iexact H3
  · iintro %v %hv
    exact hv.elim

/-- A leader's facts hold its term's leadership. -/
theorem srvFacts_isLeader (γ : RaftNames) (C : List w64) (j : w64) (v : Etcdraft.Server)
    (hl : v.state = Etcdraft.leader) :
    srvFacts (GF := GF) γ C j v ⊢ isLeader γ j (W64 v.currentTerm) := by
  unfold srvFacts; simp only [hl, ↓reduceIte]
  iintro ⟨%es, %pend, -, -, -, ⟨#H, -⟩, -⟩
  iexact H

/-- **A heartbeat is fine to send** from its term's leader (`i`, its commit index at most the
leader's): no entries, no previous entry, within the leader's durable log (`DurS`), one leader per
term. -/
theorem msgOk_heartbeat (σ : Etcdraft.State) (p : Etcdraft.Msg) (i : Etcdraft.ID)
    (hsi : TraceSpecInv.SpecInv σ) (h1 : σ.moreThanOneLeaderInv = true) (hi : i ∈ σ.server)
    (hl : (σ.s i).state = Etcdraft.leader) (hpt : p.type = .appendEntriesRequest)
    (he : p.entries = []) (hpi : p.prevLogIndex = 0) (hsrc : p.source = i)
    (hterm : p.term = (σ.s i).currentTerm) (hcm : p.commitIndex ≤ (σ.s i).commitIndex) :
    TraceSpecInv.MsgOk σ p := by
  have hdur := hsi.2.1 i hi hl
  refine ⟨?_, ?_, ⟨by rw [hsrc, hterm]; exact Int.le_refl _, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro j _ _ k e hk; rw [he] at hk; simp at hk
  · intro j hj hlj
    refine ⟨fun _ _ _ => by rw [hpi, he]; simp, ?_, ?_⟩
    · intro _ h; rw [hpt] at h; cases h
    · intro _ ht
      have hij : i = j := TraceSpecInv.oneLeader h1 hi hj hl hlj (by rw [← hterm, ht])
      subst hij
      exact Int.le_trans hcm hdur.2.1
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> rw [hpt] at h <;> cases h
  · intro j _ hc
    refine ⟨?_, ?_, ?_⟩
    · intro hs _; rw [← hs, hsrc, hl] at hc; exact absurd hc (by decide)
    · intro _ h; rw [hpt] at h; cases h
    · intro _ _ h; rw [hpt] at h; cases h
  · intro h; exact absurd he h
  · intro e h; rw [he] at h; cases h
  · intro _; exact ⟨by rw [hsrc]; exact hi, by rw [hsrc]; exact hcm⟩

/-- **The facts of a heartbeat's send line** (`FxPres`, the sufficiency check of Q15): at phases that
keep the share's server (up to `toC`) and add the specification's heartbeat `p` (canonical, from the
node, of its term as its leader, its commit at most the node's), the facts after the line follow from
those before: the heartbeat's `msgFacts` from the leader's `isLeader` in its `srvFacts`, its `MsgOk` by
`msgOk_heartbeat`, the uniqueness from `MsgsShape` (`msgsUniq_send_canon`). -/
theorem fxPres_heartbeat (γ : RaftNames) (id : w64) (E : TraceEv → Prop)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) (p : Etcdraft.Msg)
    (hp0 : canonMsg p = p) (hpt : p.type = .appendEntriesRequest) (hps : p.subtype = "heartbeat")
    (hsrc : p.source = idAbs id)
    (hC : ∀ C cs P, Φ C cs P → id ∈ C) (hdC : ∀ C cs P, Φ C cs P → p.dest ∈ confAbs C)
    (hlead : ∀ C cs P, Φ C cs P →
      cs.state = Etcdraft.leader ∧ p.term = cs.currentTerm ∧ p.commitIndex ≤ cs.commitIndex)
    (hΦ' : ∀ C cs P cs' P', Φ C cs P → Φ' C cs' (P ++ P') → cs' = cs ∧ P' = [p]) :
    ⊢ FxPres (GF := GF) γ id E Φ Φ' := by
  iunfold FxPres
  imodintro
  iintro %C %cs %P %e %a %a' %P' %σ %hpre Htbl #Hfx
  obtain ⟨hΦ, -, hcs, hΦ1, -, hsrv, hσa, -, -, -⟩ := hpre
  obtain ⟨hcs', hP'⟩ := hΦ' C cs P _ P' hΦ hΦ1
  subst hP'
  have hidC := hC C cs P hΦ
  obtain ⟨hl, ht, hcm⟩ := hlead C cs P hΦ
  rw [← hcs] at hl ht hcm
  simp only [toC] at hl ht hcm
  have hi : idAbs id ∈ σ.server := by rw [hsrv]; exact (mem_confAbs C id).2 hidC
  -- the canonical heartbeat: no previous entry, no entries
  have hpe : p.entries = [] ∧ p.prevLogIndex = 0 := by
    rw [← hp0]; unfold canonMsg; rw [hpt]; simp [hps]
  ihave #Hfx0 := Hfx
  iunfold simFx at Hfx0
  icases Hfx0 with ⟨#Hal, -, -, %Hp0⟩
  icases allFacts_oneLeader γ C σ hsrv $$ Hal with %h1
  -- the heartbeat's facts: the node leads its term
  rw [← hσa] at hl ht hcm
  iunfold allFacts at Hal
  ihave #Hsf := Hal $$ %id %hidC
  ihave #Hld := srvFacts_isLeader γ C id (σ.s (idAbs id)) hl $$ Hsf
  ihave #Hpf : msgFacts γ C p $$ []
  · unfold msgFacts; rw [if_pos hpt]
    iexists id, []
    isplitr
    · ipureintro
      refine ⟨hsrc, by rw [hpe.1]; simp [logAbs], by rw [hpe.1, hpe.2]; simp⟩
    isplitr
    · rw [ht]; iexact Hld
    · unfold logRecs; iapply Iris.BI.BigSepL.bigSepL_nil.2; iempintro
  ihave #H2 := simFx_send γ C σ p
    (msgOk_heartbeat σ p (idAbs id) Hp0.1 h1 hi hl hpt hpe.1 hpe.2 hsrc ht hcm)
    hp0 (fun _ _ _ => .inl hps) (appSliceOf_nil σ p hpe.1) (fun h => by have := h.1; rw [hpt] at this; cases this)
    ⟨by rw [hsrc]; exact hi, by rw [hsrv]; exact hdC C cs P hΦ⟩ $$ [$Hfx $Hpf]
  have hs : ∀ j, toC (σ.send p).server
      ((withNode σ (idAbs id) a' _root_.id (fun b => [p].foldl Etcdraft.Bag.with b)).s j) =
      toC (σ.send p).server ((σ.send p).s j) := by
    intro j
    show toC σ.server (if j = idAbs id then a' else σ.s j) = toC σ.server (σ.s j)
    split
    · rename_i hj; subst hj; rw [hσa, hsrv, hcs', hcs]
    · rfl
  ihave #H3 := simFx_congr γ C (σ.send p)
    (withNode σ (idAbs id) a' _root_.id (fun b => [p].foldl Etcdraft.Bag.with b))
    rfl rfl rfl hs $$ H2
  iframe Htbl
  iexact H3

/-- **An append request is fine to send** from its term's leader `i` when its entries are a slice of
`i`'s log (`hsl`) within it, its commit at most `i`'s: the leaders' entries (`LeaderEntries`), the
entries' terms (`LogTermsLe`), the durable bound (`DurS`), one leader per term. -/
theorem msgOk_app (σ : Etcdraft.State) (p : Etcdraft.Msg) (i : Etcdraft.ID)
    (hsi : TraceSpecInv.SpecInv σ) (h1 : σ.moreThanOneLeaderInv = true) (hi : i ∈ σ.server)
    (hl : (σ.s i).state = Etcdraft.leader) (hpt : p.type = .appendEntriesRequest) (hsrc : p.source = i)
    (hterm : p.term = (σ.s i).currentTerm) (hcm : p.commitIndex ≤ (σ.s i).commitIndex)
    (hpi : 0 ≤ p.prevLogIndex) (hlen : p.prevLogIndex + p.entries.length ≤ (σ.s i).log.length)
    (hsl : ∀ (k : Nat) (e : Etcdraft.Entry), p.entries[k]? = some e → (σ.s i).log[p.prevLogIndex.toNat + k]? = some e) :
    TraceSpecInv.MsgOk σ p := by
  have hdur := hsi.2.1 i hi hl
  refine ⟨?_, ?_, ⟨by rw [hsrc, hterm]; exact Int.le_refl _, ?_⟩, ?_, fun _ => hpi, ?_, ?_⟩
  · intro j hj hlj k e hk het
    have hlog := hsl k e hk
    exact (hsi.leaderEntries j hj hlj).1 i hi _ e hlog het
  · intro j hj hlj
    refine ⟨fun hs _ _ => ?_, ?_, ?_⟩
    · rw [hsrc] at hs; subst hs; exact hlen
    · intro _ h; rw [hpt] at h; cases h
    · intro _ ht
      have hij : i = j := TraceSpecInv.oneLeader h1 hi hj hl hlj (by rw [← hterm, ht])
      subst hij
      exact Int.le_trans hcm hdur.2.1
  · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> rw [hpt] at h <;> cases h
  · intro j _ hc
    refine ⟨?_, ?_, ?_⟩
    · intro hs _; rw [← hs, hsrc, hl] at hc; exact absurd hc (by decide)
    · intro _ h; rw [hpt] at h; cases h
    · intro _ _ h; rw [hpt] at h; cases h
  · intro e he
    obtain ⟨k, hk⟩ := List.getElem?_of_mem he
    have hlog := hsl k e hk
    rw [hterm]
    exact hsi.logTermsLe.1 i hi e (List.mem_of_getElem? hlog)
  · intro _; exact ⟨by rw [hsrc]; exact hi, by rw [hsrc]; exact hcm⟩

/-- **The facts of an `"app"` request's send line, with entries** (`FxPres`, the sufficiency check of
Q16): at phases that keep the share's server (up to `toC`) and add the request `p` (canonical, from the
node leading its term, its entries a slice of the node's log within it, its commit at most the node's),
the facts after the line follow from those before and the request's own facts (`msgFacts`: its
sender's leadership and its entries' records, which raft's ghost state gives the caller); the
uniqueness from `MsgsShape` and `AppSlices` (`pinned_of_slices`), `AppSlices` kept by the slice. -/
theorem fxPres_app (γ : RaftNames) (id : w64) (E : TraceEv → Prop)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) (p : Etcdraft.Msg)
    (hp0 : canonMsg p = p) (hpt : p.type = .appendEntriesRequest) (hps : p.subtype = "app")
    (hsrc : p.source = idAbs id)
    (hC : ∀ C cs P, Φ C cs P → id ∈ C) (hdC : ∀ C cs P, Φ C cs P → p.dest ∈ confAbs C)
    (hlead : ∀ C cs P, Φ C cs P →
      cs.state = Etcdraft.leader ∧ p.term = cs.currentTerm ∧ p.commitIndex ≤ cs.commitIndex ∧
      0 ≤ p.prevLogIndex ∧ p.prevLogIndex + p.entries.length ≤ cs.log.length ∧
      ∀ (k : Nat) (e : Etcdraft.Entry), p.entries[k]? = some e → cs.log[p.prevLogIndex.toNat + k]? = some e)
    (hΦ' : ∀ C cs P cs' P', Φ C cs P → Φ' C cs' (P ++ P') → cs' = cs ∧ P' = [p]) :
    (□ ∀ C cs P, ⌜Φ C cs P⌝ -∗ msgFacts γ C p : IProp GF) ⊢ FxPres (GF := GF) γ id E Φ Φ' := by
  iintro #Hmf
  iunfold FxPres
  imodintro
  iintro %C %cs %P %e %a %a' %P' %σ %hpre Htbl #Hfx
  obtain ⟨hΦ, -, hcs, hΦ1, -, hsrv, hσa, -, -, -⟩ := hpre
  obtain ⟨hcs', hP'⟩ := hΦ' C cs P _ P' hΦ hΦ1
  subst hP'
  have hidC := hC C cs P hΦ
  obtain ⟨hl, ht, hcm, hpi, hlen, hsl⟩ := hlead C cs P hΦ
  rw [← hcs] at hl ht hcm hlen hsl
  simp only [toC] at hl ht hcm hlen hsl
  rw [← hσa] at hl ht hcm hlen hsl
  have hi : idAbs id ∈ σ.server := by rw [hsrv]; exact (mem_confAbs C id).2 hidC
  ihave #Hfx0 := Hfx
  iunfold simFx at Hfx0
  icases Hfx0 with ⟨#Hal, -, -, %Hp0⟩
  icases allFacts_oneLeader γ C σ hsrv $$ Hal with %h1
  ihave #Hpf := Hmf $$ %C %cs %P %hΦ
  have hslice : AppSliceOf σ p := by
    intro _ j hj hlj htj hsj k e he
    rw [hsrc] at hsj; subst hsj; exact hsl k e he
  ihave #H2 := simFx_send γ C σ p
    (msgOk_app σ p (idAbs id) Hp0.1 h1 hi hl hpt hsrc ht hcm hpi hlen hsl)
    hp0 (pinned_of_slices σ p (idAbs id) hi hl ht.symm hsrc hps hsl Hp0.2.2.2) hslice
    (fun h => by have := h.1; rw [hpt] at this; cases this)
    ⟨by rw [hsrc]; exact hi, by rw [hsrv]; exact hdC C cs P hΦ⟩ $$ [$Hfx $Hpf]
  have hs : ∀ j, toC (σ.send p).server
      ((withNode σ (idAbs id) a' _root_.id (fun b => [p].foldl Etcdraft.Bag.with b)).s j) =
      toC (σ.send p).server ((σ.send p).s j) := by
    intro j
    show toC σ.server (if j = idAbs id then a' else σ.s j) = toC σ.server (σ.s j)
    split
    · rename_i hj; subst hj; rw [hσa, hsrv, hcs', hcs]
    · rfl
  ihave #H3 := simFx_congr γ C (σ.send p)
    (withNode σ (idAbs id) a' _root_.id (fun b => [p].foldl Etcdraft.Bag.with b))
    rfl rfl rfl hs $$ H2
  iframe Htbl
  iexact H3

end facts

end EtcdGrove
end Perennial
