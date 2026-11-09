/-
Lean-first (no Rocq counterpart). Trace-check's layer B (2026-11-09): a node event's line matches
the specification's server (`stateMatches`, `ValidatePostStates`) when the server is `R`-related to
the state raft logged.
-/
module

public import Proof.go_etcd_io.raft.v3.TraceSimStr
public import Proof.go_etcd_io.raft.v3.TraceSimLemmas
public import Proof.go_etcd_io.raft.v3.TracedHooksDraft
public import Proof.go_etcd_io.raft.v3.TraceSimRun

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

namespace TraceSim

variable [GooseExts]

/-- Raft's role strings are the specification's roles (no pre-candidate: pre-vote off). -/
theorem roleStr_abs (r : PRole) (h : r ≠ .preCandidate) : gsStr (roleStr r) = roleAbs (proleRole r) := by
  cases r <;> first | rfl | exact absurd rfl h

theorem gInt_of_lt (w : w64) (h : uint.Z w < 2 ^ 63) : gInt w = uint.Z w := by
  unfold gInt; word

theorem setIds_mk_perm_eq (xs C : List w64) (h : xs.Perm C) :
    Etcdraft.SetIds.mk (xs.map idAbs) = confAbs C := by
  unfold confAbs; apply setIds_mk_eq; intro x
  exact (h.map idAbs).mem_iff

/-- **A node event's line matches the server `R`-related to the logged state**: raft logs the
term, vote, role, last index, commit index and voters of its state `s`; the specification's server
`a`, `R`-related to `s` (the terms and indices below `2^63`, as Go's `int` reads them), has them. -/
theorem stateMatches_node (C : List w64) (s : NState) (a : Etcdraft.Server) (e : TraceEv) (id : w64)
    (xs : List w64) (hR : SimServerR C C.length (toPState s) a) (hs : LogShapeOk C.length (toPState s))
    (hpre : s.role ≠ .preCandidate)
    (hterm : e.term = s.term) (hcommit : e.commit = s.logst.committed)
    (hrole : e.role = roleStr s.role) (hlog : e.logSize = plastIndex (toPState s))
    (hxs : xs.Perm C)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63)
    (st : Etcdraft.State) (hst : st.s (idAbs id) = a) (hsrv : st.server.contains (idAbs id) = true) :
    ({ ev := evConv e, nid := idAbs id, vote := idAbs s.vote, role := (evConv e).role,
       conf := (Etcdraft.SetIds.mk (xs.map idAbs), Etcdraft.SetIds.mk (([] : List w64).map idAbs)),
       «from» := 0, to := 0 } : Etcdraft.Line).stateMatches st (idAbs id) = true := by
  obtain ⟨h1, h2, h3, -, -, h6, h7, h8, -, -, -⟩ := hR
  unfold Etcdraft.Line.stateMatches
  simp only [hsrv, hst, Bool.true_and, Bool.and_eq_true, beq_iff_eq]
  have hlen : (a.log.length : Int) = uint.Z (plastIndex (toPState s)) := by
    rw [h6, logAbs_length, plastIndex_length _ _ hs]
  refine ⟨⟨⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rw [h1]; simp only [evConv, hterm]; rw [gInt_of_lt _ bt]; rfl
  · rw [h2]; simp only [evConv, hrole]; rw [roleStr_abs _ hpre]; rfl
  · exact h3
  · rw [hlen]; simp only [evConv, hlog]; rw [gInt_of_lt _ bl]
  · rw [h7]; simp only [evConv, hcommit]; rw [gInt_of_lt _ bc]; rfl
  · rw [h8]; exact (setIds_mk_perm_eq xs C hxs).symm
  · rw [h8]; rfl

/-- A node event's line. -/
def nodeLine (e : TraceEv) (id vote : w64) (xs : List w64) : Etcdraft.Line :=
  { ev := evConv e, nid := idAbs id, vote := idAbs vote, role := (evConv e).role,
    conf := (Etcdraft.SetIds.mk (xs.map idAbs), Etcdraft.SetIds.mk (([] : List w64).map idAbs)),
    «from» := 0, to := 0 }

theorem confAbs_nodup (C : List w64) : (confAbs C).Nodup :=
  (setIds_mk_sorted _).imp (fun h => Nat.ne_of_lt h)

/-- **The `Commit` line's step** (the global part, pure): from a run reaching `σ`, raft's `Commit`
event of node `id` (the state `s` it logged, after its commit), node `id`'s server `a` a leader whose
`AdvanceCommitIndex` commits to `n`, the committed server `R`-related to `s`, the line past the
node's bootstrap lines, and the invariants at the result: the run extends to `σ.commitTo id n`. -/
theorem simRun_commit (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (id : w64) (s : NState) (cfg : CfgM)
    (hev : NodeEvOf rsmCommit id s cfg e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : id ∈ C) (a : Etcdraft.Server) (n : Int) (hσ : σ.s (idAbs id) = a) (hsrv : σ.server = confAbs C)
    (hlead : a.state = Etcdraft.leader) (hadv : AdvancesTo a n)
    (hR : SimServerR C C.length (toPState s) { a with commitIndex := max a.commitIndex n })
    (hs : LogShapeOk C.length (toPState s)) (hrole : s.role = .leader)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinv : (σ.commitTo (idAbs id) n).violated = .ok none) :
    SimRun C (L ++ [e]) (σ.commitTo (idAbs id) n) := by
  obtain ⟨hname, hnid, hterm, hvote, hcommit, hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, hmsg, -, -, -, -⟩ := hev
  have hys0 : ys = [] := by
    rw [hout] at hys
    have : elements (∅ : GSet w64) = [] :=
      List.eq_nil_of_length_eq_zero (by rw [GMap.length_elements, GMap.size_empty])
    rw [this] at hys; exact List.Perm.eq_nil hys
  subst hys0
  have hname' : gsStr e.name = "Commit" := by
    simp only [rsmCommit, evtNames] at hname
    have : e.name = go!"Commit" := by
      have := hname; simp at this; exact this.symm
    rw [this]; rfl
  have hconf' : e.conf = (xs.map decStr, ([] : List w64).map decStr) := hconf
  generalize hln : nodeLine e id s.vote xs = ln
  have hparse : Etcdraft.parseLine L.length (evConv e) = .ok ln :=
    hln ▸ parseLine_node L.length e id s.vote xs [] hnid hvote hconf' hmsg (by rw [hname']; rfl) (by rw [hname']; decide)
  have hmatch : ln.stateMatches (σ.commitTo (idAbs id) n) (idAbs id) = true := by
    rw [← hln]
    apply stateMatches_node C s _ e id xs hR hs (by rw [hrole]; decide) hterm hcommit hrl hlog
      (hxs.trans hin) bt bc bl
    · simp [Etcdraft.State.commitTo, Etcdraft.State.upd, hσ]
    · simp only [Etcdraft.State.commitTo, Etcdraft.State.upd]; rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  apply simRun_snoc_single C L σ _ e ln hrun hL hparse _ hinv
  intro lines ts hl hts hl'
  have hlen := parseLines_length _ _ hl
  simp only [List.length_map] at hlen
  have hline : (linesTrace C (lines ++ [ln])).line ts.l = ln := by
    simp only [linesTrace, Etcdraft.Trace.line, hl', List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [hlen]
  apply next_commit _ ts (idAbs id) _ (by omega)
  · simp [linesTrace, Etcdraft.Trace.len]; omega
  · simp only [linesTrace]; rw [hl']; simpa using hboot lines ln hl
  · rw [hline, ← hln]; simp [nodeLine, evConv, hname']
  · rw [hline, ← hln]; rfl
  · exact confAbs_nodup C
  · simp only [linesTrace]; rw [mem_confAbs]; exact hC
  · rw [hts]; exact hadv σ (idAbs id) hσ
  · rw [hline]; exact hmatch
  · rw [hline, ← hln]; simp only [nodeLine, evConv, hrl, hrole]; rfl
  · rw [hts, hσ]; exact hlead

/-- The last line of the lines' trace with a line appended. -/
theorem linesTrace_line_last (C : List w64) (lines : List Etcdraft.Line) (ln : Etcdraft.Line) (l : Nat)
    (hl : l = lines.length + 1) : (linesTrace C (lines ++ [ln])).line l = ln := by
  simp only [linesTrace, Etcdraft.Trace.line, hl, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega)]
  simp

/-- **A node line's step** (the global part, pure, generic): from a run reaching `σ`, a node event
of raft whose line (`nodeLine`) has, from the run's end, the one non-receive successor `σ'`, past
the node's bootstrap lines, with the invariants at `σ'`: the run extends to `σ'`. -/
theorem simRun_node (C : List w64) (L : List TraceEv) (σ σ' : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (id vote : w64) (xs : List w64)
    (hnid : e.nid = decStr id) (hvote : e.vote = decStr vote)
    (hconf : e.conf = (xs.map decStr, ([] : List w64).map decStr)) (hmsg : e.msg = none)
    (hrecv : Etcdraft.isReceiveName (gsStr e.name) = false)
    (hmev : Etcdraft.isMessageEvent (gsStr e.name) = false) (hcc : gsStr e.name ≠ "ChangeConf")
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hnr : ∀ lines (ts : Etcdraft.TState), parseLines (L.map evConv) = .ok lines → ts.s = σ →
      ts.l = L.length + 1 →
      (linesTrace C (lines ++ [nodeLine e id vote xs])).nonReceive ts = .ok [σ'])
    (hinv : σ'.violated = .ok none) :
    SimRun C (L ++ [e]) σ' := by
  have hparse : Etcdraft.parseLine L.length (evConv e) = .ok (nodeLine e id vote xs) :=
    parseLine_node L.length e id vote xs [] hnid hvote hconf hmsg hmev hcc
  apply simRun_snoc_single C L σ σ' e _ hrun hL hparse _ hinv
  intro lines ts hl hts hl'
  have hlen := parseLines_length _ _ hl
  simp only [List.length_map] at hlen
  apply next_of_nonReceive _ ts σ' (by omega)
  · simp [linesTrace, Etcdraft.Trace.len]; omega
  · simp only [linesTrace]; rw [hl']; simpa using hboot lines _ hl
  · rw [linesTrace_line_last C lines _ _ (by omega)]; simpa [nodeLine, evConv] using hrecv
  · exact hnr lines ts hl hts hl'

theorem upd_self (st : Etcdraft.State) (i : Etcdraft.ID) (f : Etcdraft.Server → Etcdraft.Server) :
    (st.upd i f).s i = f (st.s i) := by simp [Etcdraft.State.upd]

theorem upd_server (st : Etcdraft.State) (i : Etcdraft.ID) (f : Etcdraft.Server → Etcdraft.Server) :
    (st.upd i f).server = st.server := rfl

/-- The server a `BecomeLeader` makes of a candidate. -/
def leaderOf (i : Etcdraft.ID) (v : Etcdraft.Server) : Etcdraft.Server :=
  { v with state := Etcdraft.leader, lead := i,
           matchIndex := fun j => if j = i then (v.log.length : Int) else 0 }

/-- **The `BecomeLeader` line's step**: node `id`'s server a candidate with a quorum of granted votes
(the won tally: the simulation's ghost), the leader it becomes `R`-related to the state raft logged
(after `reset`). -/
theorem simRun_becomeLeader (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (id : w64) (s : NState) (cfg : CfgM)
    (hev : NodeEvOf (W64 3) id s cfg e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : id ∈ C) (a : Etcdraft.Server) (hσ : σ.s (idAbs id) = a) (hsrv : σ.server = confAbs C)
    (hcand : a.state = Etcdraft.candidate) (hcfg : a.config.incoming = confAbs C)
    (hq : Etcdraft.isQuorum a.votesGranted (confAbs C) = true)
    (hR : SimServerR C C.length (toPState s) (leaderOf (idAbs id) a))
    (hs : LogShapeOk C.length (toPState s)) (hrole : s.role = .leader)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinv : (σ.upd (idAbs id) (leaderOf (idAbs id))).violated = .ok none) :
    SimRun C (L ++ [e]) (σ.upd (idAbs id) (leaderOf (idAbs id))) := by
  obtain ⟨hname, hnid, hterm, hvote, hcommit, hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, hmsg, -, -, -, -⟩ := hev
  have hys0 : ys = [] := by
    rw [hout] at hys
    have : elements (∅ : GSet w64) = [] :=
      List.eq_nil_of_length_eq_zero (by rw [GMap.length_elements, GMap.size_empty])
    rw [this] at hys; exact List.Perm.eq_nil hys
  subst hys0
  have hname' : gsStr e.name = "BecomeLeader" := by
    simp only [evtNames] at hname
    have : e.name = go!"BecomeLeader" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  have hbl : σ.becomeLeader (idAbs id) = some (σ.upd (idAbs id) (leaderOf (idAbs id))) := by
    unfold Etcdraft.State.becomeLeader Etcdraft.State.getConfig
    rw [hσ]; simp only [hcand, hcfg, hq, beq_self_eq_true, Bool.and_self, ↓reduceIte]
    rfl
  apply simRun_node C L σ _ hrun hL e id s.vote xs hnid hvote hconf hmsg (by rw [hname']; rfl)
    (by rw [hname']; rfl) (by rw [hname']; decide) hboot _ hinv
  intro lines ts hl hts hl'
  have hlen := parseLines_length _ _ hl
  simp only [List.length_map] at hlen
  have hline := linesTrace_line_last C lines (nodeLine e id s.vote xs) ts.l (by omega)
  apply nonReceive_becomeLeader _ ts (idAbs id) _ (by simp [linesTrace, Etcdraft.Trace.len]; omega)
  · rw [hline]; simp [nodeLine, evConv, hname']
  · rw [hline]; rfl
  · exact confAbs_nodup C
  · simp only [linesTrace]; rw [mem_confAbs]; exact hC
  · rw [hts]; exact hbl
  · rw [hline]
    apply stateMatches_node C s _ e id xs hR hs (by rw [hrole]; decide) hterm hcommit hrl hlog
      (hxs.trans hin) bt bc bl
    · rw [upd_self, hσ]
    · rw [upd_server, hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  · rw [hline]; simp only [nodeLine, evConv, hrl, hrole]; rfl
  · rw [upd_self]; rfl

/-- **The `Replicate` line's step**: node `id`'s server a leader; the specification's
`ClientRequest(i, 0)` (no state check at a `Replicate` line). -/
theorem simRun_replicate (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (id : w64) (s : NState) (cfg : CfgM)
    (hev : NodeEvOf (W64 5) id s cfg e) (hout : cfg.outgoing = ∅)
    (hC : id ∈ C) (hlead : (σ.s (idAbs id)).state = Etcdraft.leader)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinv : (σ.replicate (idAbs id) (.val 0) .value).violated = .ok none) :
    SimRun C (L ++ [e]) (σ.replicate (idAbs id) (.val 0) .value) := by
  obtain ⟨hname, hnid, -, hvote, -, -, -, ⟨xs, ys, -, hys, hconf⟩, hmsg, -, -, -, -⟩ := hev
  have hys0 : ys = [] := by
    rw [hout] at hys
    have : elements (∅ : GSet w64) = [] :=
      List.eq_nil_of_length_eq_zero (by rw [GMap.length_elements, GMap.size_empty])
    rw [this] at hys; exact List.Perm.eq_nil hys
  subst hys0
  have hname' : gsStr e.name = "Replicate" := by
    simp only [evtNames] at hname
    have : e.name = go!"Replicate" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  have hcr : σ.clientRequest (idAbs id) 0 = some (σ.replicate (idAbs id) (.val 0) .value) := by
    unfold Etcdraft.State.clientRequest; simp [hlead]
  apply simRun_node C L σ _ hrun hL e id s.vote xs hnid hvote hconf hmsg (by rw [hname']; rfl)
    (by rw [hname']; rfl) (by rw [hname']; decide) hboot _ hinv
  intro lines ts hl hts hl'
  have hlen := parseLines_length _ _ hl
  simp only [List.length_map] at hlen
  have hline := linesTrace_line_last C lines (nodeLine e id s.vote xs) ts.l (by omega)
  apply nonReceive_replicate _ ts (idAbs id) _ (by simp [linesTrace, Etcdraft.Trace.len]; omega)
  · rw [hline]; simp [nodeLine, evConv, hname']
  · rw [hline]; rfl
  · exact confAbs_nodup C
  · simp only [linesTrace]; rw [mem_confAbs]; exact hC
  · rw [hts]; exact hcr

/-- The server a `Timeout` makes. -/
def candOf (i : Etcdraft.ID) (v : Etcdraft.Server) : Etcdraft.Server :=
  { v with state := Etcdraft.candidate, currentTerm := v.currentTerm + 1, votedFor := i, lead := Etcdraft.nil,
           votesResponded := [], votesGranted := [] }

/-- **The `BecomeCandidate` line's step**: node `id`'s server a follower or candidate of the
configuration (pre-vote off), the candidate it becomes of the term raft logged. -/
theorem simRun_becomeCandidate (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (id : w64) (s : NState) (cfg : CfgM)
    (hev : NodeEvOf (W64 1) id s cfg e) (hout : cfg.outgoing = ∅)
    (hC : id ∈ C) (a : Etcdraft.Server) (hσ : σ.s (idAbs id) = a) (hpv : σ.preVote = false)
    (hrl : a.state = Etcdraft.follower ∨ a.state = Etcdraft.candidate) (hcfg : a.config.incoming = confAbs C)
    (hrole : s.role = .candidate) (hterm : a.currentTerm + 1 = uint.Z s.term) (bt : uint.Z s.term < 2 ^ 63)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinv : (σ.upd (idAbs id) (candOf (idAbs id))).violated = .ok none) :
    SimRun C (L ++ [e]) (σ.upd (idAbs id) (candOf (idAbs id))) := by
  obtain ⟨hname, hnid, hterm', hvote, -, hrl', -, ⟨xs, ys, -, hys, hconf⟩, hmsg, -, -, -, -⟩ := hev
  have hys0 : ys = [] := by
    rw [hout] at hys
    have : elements (∅ : GSet w64) = [] :=
      List.eq_nil_of_length_eq_zero (by rw [GMap.length_elements, GMap.size_empty])
    rw [this] at hys; exact List.Perm.eq_nil hys
  subst hys0
  have hname' : gsStr e.name = "BecomeCandidate" := by
    simp only [evtNames] at hname
    have : e.name = go!"BecomeCandidate" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  have hto : σ.timeout (idAbs id) = some (σ.upd (idAbs id) (candOf (idAbs id))) := by
    unfold Etcdraft.State.timeout Etcdraft.State.timeoutEnabled Etcdraft.Server.timeoutRoleOk
      Etcdraft.State.getConfig
    have hcont : (confAbs C).contains (idAbs id) = true := by
      rw [List.contains_iff_mem, mem_confAbs]; exact hC
    rw [hσ]
    rcases hrl with h | h <;> simp only [h, hcfg, hcont, hpv, beq_self_eq_true, Bool.true_or, Bool.or_true,
      Bool.true_and, Bool.not_false, ↓reduceIte] <;> rfl
  apply simRun_node C L σ _ hrun hL e id s.vote xs hnid hvote hconf hmsg (by rw [hname']; rfl)
    (by rw [hname']; rfl) (by rw [hname']; decide) hboot _ hinv
  intro lines ts hl hts hl'
  have hlen := parseLines_length _ _ hl
  simp only [List.length_map] at hlen
  have hline := linesTrace_line_last C lines (nodeLine e id s.vote xs) ts.l (by omega)
  apply nonReceive_becomeCandidate _ ts (idAbs id) _ (by simp [linesTrace, Etcdraft.Trace.len]; omega)
  · rw [hline]; simp [nodeLine, evConv, hname']
  · rw [hline]; rfl
  · exact confAbs_nodup C
  · simp only [linesTrace]; rw [mem_confAbs]; exact hC
  · rw [hts]; exact hto
  · rw [hline]; simp only [nodeLine, evConv, hrl', hrole]; rfl
  · rw [upd_self]; rfl
  · rw [upd_self, hline, hσ]; simp only [candOf, nodeLine, evConv, hterm']; rw [gInt_of_lt _ bt, hterm]

/-- **The `Ready` line's step**: the specification's `Ready(i)` (no state check). -/
theorem simRun_ready (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (id : w64) (s : NState) (cfg : CfgM)
    (hev : NodeEvOf (W64 8) id s cfg e) (hout : cfg.outgoing = ∅) (hC : id ∈ C)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinv : (σ.ready (idAbs id)).violated = .ok none) :
    SimRun C (L ++ [e]) (σ.ready (idAbs id)) := by
  obtain ⟨hname, hnid, -, hvote, -, -, -, ⟨xs, ys, -, hys, hconf⟩, hmsg, -, -, -, -⟩ := hev
  have hys0 : ys = [] := by
    rw [hout] at hys
    have : elements (∅ : GSet w64) = [] :=
      List.eq_nil_of_length_eq_zero (by rw [GMap.length_elements, GMap.size_empty])
    rw [this] at hys; exact List.Perm.eq_nil hys
  subst hys0
  have hname' : gsStr e.name = "Ready" := by
    simp only [evtNames] at hname
    have : e.name = go!"Ready" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  apply simRun_node C L σ _ hrun hL e id s.vote xs hnid hvote hconf hmsg (by rw [hname']; rfl)
    (by rw [hname']; rfl) (by rw [hname']; decide) hboot _ hinv
  intro lines ts hl hts hl'
  have hlen := parseLines_length _ _ hl
  simp only [List.length_map] at hlen
  have hline := linesTrace_line_last C lines (nodeLine e id s.vote xs) ts.l (by omega)
  rw [← hts]
  apply nonReceive_ready _ ts (idAbs id) (by simp [linesTrace, Etcdraft.Trace.len]; omega)
  · rw [hline]; simp [nodeLine, evConv, hname']
  · rw [hline]; rfl
  · exact confAbs_nodup C
  · simp only [linesTrace]; rw [mem_confAbs]; exact hC

/-! ### Message lines -/

/-- `MessageType.String()` of the traced types. -/
def msgTypeStr : MsgType → GoString
  | .vote => go!"MsgVote"
  | .voteResp => go!"MsgVoteResp"
  | .app => go!"MsgApp"
  | .appResp => go!"MsgAppResp"
  | .heartbeat => go!"MsgHeartbeat"
  | .heartbeatResp => go!"MsgHeartbeatResp"
  | _ => go!""

/-- The traced message `tm` of raft's message `m` (`makeTracingMessage`, a non-snapshot). -/
def MsgEvOf (m : Msg) (tm : TraceMsg) : Prop :=
  tm.typ = msgTypeStr m.ty ∧ tm.term = m.term ∧ tm.frm = decStr m.src ∧ tm.to = decStr m.dst ∧
  tm.entries = W64 m.entries.length ∧ tm.logTerm = m.logterm ∧ tm.index = m.index ∧
  tm.commit = m.commit ∧ tm.reject = m.reject

/-- A message event's line. -/
def msgLine (e : TraceEv) (id vote f d : w64) (xs : List w64) : Etcdraft.Line :=
  { ev := evConv e, nid := idAbs id, vote := idAbs vote, role := (evConv e).role,
    conf := (Etcdraft.SetIds.mk (xs.map idAbs), Etcdraft.SetIds.mk (([] : List w64).map idAbs)),
    «from» := idAbs f, to := idAbs d }

/-- A fold appending each element's results, where one element gives one result and the others
none. -/
theorem foldlM_append_single {α β ε : Type} [DecidableEq α] (l : List α) (f : α → Except ε (List β))
    (a : α) (x : β) (hnd : l.Nodup) (ha : a ∈ l) (hfa : f a = .ok [x]) (hf : ∀ b ∈ l, b ≠ a → f b = .ok []) :
    l.foldlM (fun acc p => do return acc ++ (← f p)) [] = .ok [x] := by
  suffices ∀ (l : List α) (acc : List β), l.Nodup → (∀ b ∈ l, b ≠ a → f b = .ok []) →
      l.foldlM (fun acc p => do return acc ++ (← f p)) acc = .ok (if a ∈ l then acc ++ [x] else acc) by
    have := this l [] hnd hf; simpa [ha] using this
  intro l
  induction l with
  | nil => intro acc _ _; simp [pure, Except.pure]
  | cons b l ih =>
    intro acc hnd hf
    rw [List.nodup_cons] at hnd
    simp only [List.foldlM_cons, bind, Except.bind, pure, Except.pure] at ih ⊢
    by_cases hb : b = a
    · subst hb
      rw [hfa]
      simp only
      rw [ih _ hnd.2 (fun c hc hne => hf c (by simp [hc]) hne)]
      simp [hnd.1]
    · rw [hf b (by simp) hb]
      simp only [List.append_nil]
      rw [ih _ hnd.2 (fun c hc hne => hf c (by simp [hc]) hne)]
      simp [Ne.symm hb]

theorem mem_pairs (t : Etcdraft.Trace) (i j : Etcdraft.ID) : (i, j) ∈ t.pairs ↔ i ∈ t.server ∧ j ∈ t.server := by
  unfold Etcdraft.Trace.pairs; simp

theorem product_nodup (l s : List Etcdraft.ID) (hl : l.Nodup) (hs : s.Nodup) :
    (l.flatMap (fun i => s.map (fun j => (i, j)))).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨hs.map (f := fun j => (a, j)) (fun _ _ hab e => hab (by simpa using e)), ih hl.2, ?_⟩
    intro x hx y hy hxy
    simp only [List.mem_map] at hx; obtain ⟨_, _, rfl⟩ := hx
    simp only [List.mem_flatMap, List.mem_map] at hy; obtain ⟨b, hb, _, _, rfl⟩ := hy
    simp only [Prod.mk.injEq] at hxy
    exact hl.1 (hxy.1 ▸ hb)

theorem pairs_nodup (t : Etcdraft.Trace) (h : t.server.Nodup) : t.pairs.Nodup := by
  unfold Etcdraft.Trace.pairs; exact product_nodup _ _ h h

theorem gsStr_msgTypeStr_hb : gsStr (msgTypeStr .heartbeat) = "MsgHeartbeat" := by rfl

/-- **A heartbeat's line predicate** (`LoglineIsAppendEntriesRequest` of the heartbeat's
abstraction): the logged message is raft's heartbeat (its term and commit below `2^63`). -/
theorem isAER_heartbeat (C : List w64) (bl : Nat) (e : TraceEv) (id vote : w64) (xs : List w64) (m : Msg)
    (tm : TraceMsg) (hmsg : e.msg = some tm) (hm : MsgEvOf m tm) (hty : m.ty = .heartbeat)
    (hents : m.entries = []) (bt : uint.Z m.term < 2 ^ 63) (bc : uint.Z m.commit < 2 ^ 63) :
    (msgLine e id vote m.src m.dst xs).isAppendEntriesRequest
      ((msgAbs C bl m).get (by simp [msgAbs, hty])) = true := by
  obtain ⟨htyp, hterm, -, -, hent, -, -, hcommit, -⟩ := hm
  have hmsg' : (msgAbs C bl m) = some
      { type := .appendEntriesRequest, subtype := "heartbeat", term := uint.Z m.term,
        commitIndex := uint.Z m.commit, source := idAbs m.src, dest := idAbs m.dst } := by
    simp only [msgAbs, hty]
  simp only [hmsg', Option.get_some]
  unfold Etcdraft.Line.isAppendEntriesRequest
  simp only [msgLine, evConv, hmsg, Option.map_some]
  rw [htyp, hty, hterm, hcommit, hent, hents, gInt_of_lt _ bt, gInt_of_lt _ bc, gsStr_msgTypeStr_hb]
  simp [Etcdraft.raftMsgType, Etcdraft.raftMsgSubtype]
  rfl

/-- A heartbeat line's non-receive successors: the specification's `Heartbeat(i, j)` of the line's
sender and receiver, when it matches the line. -/
theorem nonReceive_heartbeat (t : Etcdraft.Trace) (ts : Etcdraft.TState) (i j : Etcdraft.ID)
    (s2 : Etcdraft.State) (hl : ts.l ≤ t.len)
    (hname : (t.line ts.l).ev.name = "SendAppendEntriesRequest")
    (hfrom : (t.line ts.l).from = i) (hto : (t.line ts.l).to = j)
    (hty : (t.line ts.l).ev.msg.map Etcdraft.EventMsg.type = some "MsgHeartbeat")
    (hnd : t.server.Nodup) (hi : i ∈ t.server) (hj : j ∈ t.server)
    (hhb : ts.s.heartbeat i j = .ok (some s2)) (hv : t.validateAfterAppendEntries ts s2 i = true) :
    t.nonReceive ts = .ok [s2] := by
  have hsome : (t.line ts.l).ev.msg.isSome = true := by
    cases h : (t.line ts.l).ev.msg with
    | none => rw [h] at hty; cases hty
    | some _ => rfl
  have hf : t.pairs.foldlM (fun acc p => do return acc ++ (← t.heartbeatIfLogged ts p.1 p.2)) [] = .ok [s2] := by
    apply foldlM_append_single _ _ (i, j) s2 (pairs_nodup t hnd) ((mem_pairs t i j).2 ⟨hi, hj⟩)
    · simp [Etcdraft.Trace.heartbeatIfLogged, Etcdraft.Trace.isMessageEvent, Etcdraft.Trace.isEvent,
        hl, hname, hfrom, hto, hty, hsome, hhb, hv, bind, Except.bind, pure, Except.pure]
    · rintro ⟨a, b⟩ _ hne
      have : ¬ (a = i ∧ b = j) := fun h => hne (by rw [h.1, h.2])
      simp only [Etcdraft.Trace.heartbeatIfLogged, Etcdraft.Trace.isMessageEvent, Etcdraft.Trace.isEvent,
        hfrom, hto]
      by_cases ha : a = i
      · have hb : b ≠ j := fun hb => this ⟨ha, hb⟩
        simp [ha, Ne.symm hb, pure, Except.pure]
      · simp [Ne.symm ha, pure, Except.pure]
  unfold Etcdraft.Trace.nonReceive
  simp only [hname, hty]
  simp only [bind, Except.bind] at hf ⊢
  rw [hf]
  simp [Etcdraft.Trace.skipUnusedLogline, Etcdraft.Trace.isEvent, hname,
    Etcdraft.Trace.isBecomeFollowerInUpdateTermOrReturnToFollower, pure, Except.pure]

/-- **A non-receive message line's step** (generic): from a run reaching `σ`, a message event of
raft whose line (`msgLine`) has, from the run's end, the one non-receive successor `σ'`, past the
node's bootstrap lines, with the invariants at `σ'`. -/
theorem simRun_msg (C : List w64) (L : List TraceEv) (σ σ' : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (id vote f d : w64) (xs : List w64) (tm : TraceMsg)
    (hnid : e.nid = decStr id) (hvote : e.vote = decStr vote)
    (hconf : e.conf = (xs.map decStr, ([] : List w64).map decStr)) (hmsg : e.msg = some tm)
    (hfrm : tm.frm = decStr f) (hto : tm.to = decStr d)
    (htyp : (Etcdraft.raftMsgType (gsStr tm.typ)).isSome = true)
    (hrecv : Etcdraft.isReceiveName (gsStr e.name) = false) (hcc : gsStr e.name ≠ "ChangeConf")
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hnr : ∀ lines (ts : Etcdraft.TState), parseLines (L.map evConv) = .ok lines → ts.s = σ →
      ts.l = L.length + 1 →
      (linesTrace C (lines ++ [msgLine e id vote f d xs])).nonReceive ts = .ok [σ'])
    (hinv : σ'.violated = .ok none) :
    SimRun C (L ++ [e]) σ' := by
  have hparse : Etcdraft.parseLine L.length (evConv e) = .ok (msgLine e id vote f d xs) :=
    parseLine_msg L.length e id vote f d xs [] tm hnid hvote hconf hmsg hfrm hto htyp hcc
  apply simRun_snoc_single C L σ σ' e _ hrun hL hparse _ hinv
  intro lines ts hl hts hl'
  have hlen := parseLines_length _ _ hl
  simp only [List.length_map] at hlen
  apply next_of_nonReceive _ ts σ' (by omega)
  · simp [linesTrace, Etcdraft.Trace.len]; omega
  · simp only [linesTrace]; rw [hl']; simpa using hboot lines _ hl
  · rw [linesTrace_line_last C lines _ _ (by omega)]; simpa [msgLine, evConv] using hrecv
  · exact hnr lines ts hl hts hl'

/-- The events `traceSendMessage(r, m)` may log for a traced message `m` (`traceEvent` with the
message; its properties unconstrained). -/
def SendEvOf (evt : w64) (id : w64) (s : NState) (c : CfgM) (m : Msg) (e : TraceEv) : Prop :=
  evtNames[uint.nat evt]? = some e.name ∧
  e.nid = decStr id ∧ e.term = s.term ∧ e.vote = decStr s.vote ∧ e.commit = s.logst.committed ∧
  e.role = roleStr s.role ∧ e.logSize = plastIndex (toPState s) ∧
  (∃ xs ys : List w64, xs ≡ₚ elements c.incoming ∧ ys ≡ₚ elements c.outgoing ∧
    e.conf = (xs.map decStr, ys.map decStr)) ∧
  (∃ tm, e.msg = some tm ∧ MsgEvOf m tm) ∧ e.cc = none

theorem elements_empty_nil : elements (∅ : GSet w64) = [] :=
  List.eq_nil_of_length_eq_zero (by rw [GMap.length_elements, GMap.size_empty])

/-- **A heartbeat line's step**: a leader's heartbeat (its commit `min(Match, committed)`), the
specification's `Heartbeat(i, j)`; the leader's server unchanged, `R`-related to the state raft
logged. -/
theorem simRun_heartbeat (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (id : w64) (s : NState) (cfg : CfgM) (m : Msg)
    (hev : SendEvOf (W64 9) id s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : id ∈ C) (hdC : m.dst ∈ C) (hsrv : σ.server = confAbs C)
    (hR : SimServerR C C.length (toPState s) (σ.s (idAbs id))) (hs : LogShapeOk C.length (toPState s))
    (hrole : s.role = .leader) (hty : m.ty = .heartbeat) (hsrc : m.src = id) (hdst : m.dst ≠ id)
    (hterm : m.term = s.term) (hents : m.entries = [])
    (hcommit : uint.Z m.commit = min (uint.Z (toPState s).commit) (uint.Z (matchOf (toPState s) m.dst)))
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (bmc : uint.Z m.commit < 2 ^ 63)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinv : (σ.send ((msgAbs C C.length m).get (by simp [msgAbs, hty]))).violated = .ok none) :
    SimRun C (L ++ [e]) (σ.send ((msgAbs C C.length m).get (by simp [msgAbs, hty]))) := by
  obtain ⟨hname, hnid, hterm', hvote, hcommit', hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  have hname' : gsStr e.name = "SendAppendEntriesRequest" := by
    simp only [evtNames] at hname
    have : e.name = go!"SendAppendEntriesRequest" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  have htyp : tm.typ = msgTypeStr .heartbeat := by rw [hm.1, hty]
  have hhb := heartbeat_send σ C C.length (toPState s) id m hR (by simp [toPState, hrole, proleRole]) hty hsrc
    hdst hdC (by rw [hterm]; rfl) hcommit
  apply simRun_msg C L σ _ hrun hL e id s.vote m.src m.dst xs tm hnid hvote hconf hmsg hm.2.2.1 hm.2.2.2.1
    (by rw [htyp]; rfl) (by rw [hname']; rfl) (by rw [hname']; decide) hboot _ hinv
  intro lines ts hl hts hl'
  have hlen := parseLines_length _ _ hl
  simp only [List.length_map] at hlen
  have hline := linesTrace_line_last C lines (msgLine e id s.vote m.src m.dst xs) ts.l (by omega)
  apply nonReceive_heartbeat _ ts (idAbs m.src) (idAbs m.dst) _ (by simp [linesTrace, Etcdraft.Trace.len]; omega)
  · rw [hline]; simp [msgLine, evConv, hname']
  · rw [hline]; rfl
  · rw [hline]; rfl
  · rw [hline]; simp [msgLine, evConv, hmsg, htyp]; rfl
  · exact confAbs_nodup C
  · simp only [linesTrace]; rw [mem_confAbs, hsrc]; exact hC
  · simp only [linesTrace]; rw [mem_confAbs]; exact hdC
  · rw [hts, hsrc]; exact hhb
  · unfold Etcdraft.Trace.validateAfterAppendEntries Etcdraft.Trace.validatePostStates
    rw [hline, hts, Bool.and_eq_true]
    constructor
    · rw [hsrc]
      have := stateMatches_node C s (σ.s (idAbs id)) e id xs hR hs (by rw [hrole]; decide) hterm' hcommit' hrl
        hlog (hxs.trans hin) bt bc bl σ rfl (by rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC)
      unfold Etcdraft.Line.stateMatches at this ⊢
      simpa [Etcdraft.State.send, msgLine, nodeLine] using this
    · apply newPending_send
      have := isAER_heartbeat C C.length e id s.vote xs m tm hmsg hm hty hents (by rw [hterm]; exact bt) bmc
      rw [hsrc] at this ⊢
      exact this

/-- **A reply's send line is skipped** (`SendAppendEntriesResponse`/`SendRequestVoteResponse` to
another node: the receive line queued the reply): its one non-receive successor is the state itself. -/
theorem nonReceive_skipResp (t : Etcdraft.Trace) (ts : Etcdraft.TState) (hl : ts.l ≤ t.len)
    (hname : (t.line ts.l).ev.name = "SendAppendEntriesResponse" ∨
      (t.line ts.l).ev.name = "SendRequestVoteResponse")
    (hft : (t.line ts.l).from ≠ (t.line ts.l).to)
    (hmsg : ∃ em, (t.line ts.l).ev.msg = some em ∧ em.from ≠ em.to) :
    t.nonReceive ts = .ok [ts.s] := by
  obtain ⟨em, hem, hne⟩ := hmsg
  have hskip : t.skipUnusedLogline ts = true := by
    unfold Etcdraft.Trace.skipUnusedLogline Etcdraft.Trace.isEvent
    rcases hname with h | h <;> simp [h, hl, hem, hne]
  unfold Etcdraft.Trace.nonReceive
  rcases hname with h | h
  · have hf : t.server.flatMap (t.appendEntriesToSelfIfLogged ts) = [] := by
      rw [List.flatMap_eq_nil_iff]; intro i _
      simp only [Etcdraft.Trace.appendEntriesToSelfIfLogged, Etcdraft.Trace.isMessageEvent, Etcdraft.Trace.isEvent]
      by_cases hi : (t.line ts.l).from = i
      · have : (t.line ts.l).to ≠ i := fun h' => hft (hi.trans h'.symm)
        simp [hi]; intros; simp_all
      · simp; intros; simp_all
    simp only [h, hf, hskip]
    simp [pure, Except.pure, bind, Except.bind]
  · have hf : t.pairs.flatMap (fun p => t.requestVoteIfLogged ts p.1 p.2) = [] := by
      rw [List.flatMap_eq_nil_iff]; rintro ⟨i, j⟩ _
      simp only [Etcdraft.Trace.requestVoteIfLogged, Etcdraft.Trace.isMessageEvent, Etcdraft.Trace.isEvent, h]
      by_cases hi : (t.line ts.l).from = i
      · by_cases hj : (t.line ts.l).to = j
        · have : i ≠ j := fun hij => hft (by rw [hi, hj, hij])
          simp [this]
        · simp; intros; simp_all
      · simp; intros; simp_all
    simp only [h, hf, hskip]
    simp [pure, Except.pure, bind, Except.bind]

/-- **A reply's send line's step**: a response raft sends to another node (the receive line already
queued it in the specification): the state stays. -/
theorem simRun_skipResp (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (id : w64) (s : NState) (cfg : CfgM) (m : Msg) (evt : w64)
    (hevt : evt = W64 11 ∨ evt = W64 15)
    (hev : SendEvOf evt id s cfg m e) (hout : cfg.outgoing = ∅) (hne : m.src ≠ m.dst)
    (htr : m.ty = .appResp ∨ m.ty = .heartbeatResp ∨ m.ty = .voteResp)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinv : σ.violated = .ok none) :
    SimRun C (L ++ [e]) σ := by
  obtain ⟨hname, hnid, -, hvote, -, -, -, ⟨xs, ys, -, hys, hconf⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  have hname' : gsStr e.name = "SendAppendEntriesResponse" ∨ gsStr e.name = "SendRequestVoteResponse" := by
    simp only [evtNames] at hname
    rcases hevt with rfl | rfl
    · left
      have : e.name = go!"SendAppendEntriesResponse" := by have := hname; simp at this; exact this.symm
      rw [this]; rfl
    · right
      have : e.name = go!"SendRequestVoteResponse" := by have := hname; simp at this; exact this.symm
      rw [this]; rfl
  have hne' : idAbs m.src ≠ idAbs m.dst := fun h => hne (idAbs_inj.1 h)
  have htyp : (Etcdraft.raftMsgType (gsStr tm.typ)).isSome = true := by
    rw [hm.1]; rcases htr with h | h | h <;> rw [h] <;> rfl
  apply simRun_msg C L σ σ hrun hL e id s.vote m.src m.dst xs tm hnid hvote hconf hmsg hm.2.2.1 hm.2.2.2.1
    htyp (by rcases hname' with h | h <;> rw [h] <;> rfl) (by rcases hname' with h | h <;> rw [h] <;> decide)
    hboot _ hinv
  intro lines ts hl hts hl'
  have hlen := parseLines_length _ _ hl
  simp only [List.length_map] at hlen
  have hline := linesTrace_line_last C lines (msgLine e id s.vote m.src m.dst xs) ts.l (by omega)
  rw [← hts]
  apply nonReceive_skipResp _ ts (by simp [linesTrace, Etcdraft.Trace.len]; omega)
  · rw [hline]; simpa [msgLine, evConv] using hname'
  · rw [hline]; exact hne'
  · rw [hline]
    refine ⟨_, by simp [msgLine, evConv, hmsg]; rfl, ?_⟩
    simp only [hm.2.2.1, hm.2.2.2.1]
    intro h
    exact hne' (by
      have h1 := parseID_decStr m.src; have h2 := parseID_decStr m.dst
      rw [h] at h1; rw [h1] at h2; exact Option.some.inj h2)

theorem gsStr_msgTypeStr_vote : gsStr (msgTypeStr .vote) = "MsgVote" := by rfl

/-- **A vote request's line predicate** (`LoglineIsRequestVoteRequest` of its abstraction). -/
theorem isRVReq_vote (C : List w64) (bl : Nat) (e : TraceEv) (id vote : w64) (xs : List w64) (m : Msg)
    (tm : TraceMsg) (hmsg : e.msg = some tm) (hm : MsgEvOf m tm) (hty : m.ty = .vote)
    (bt : uint.Z m.term < 2 ^ 63) (bi : uint.Z m.index < 2 ^ 63) (blt : uint.Z m.logterm < 2 ^ 63) :
    (msgLine e id vote m.src m.dst xs).isRequestVoteRequest
      ((msgAbs C bl m).get (by simp [msgAbs, hty])) = true := by
  obtain ⟨htyp, hterm, -, -, -, hlt, hidx, -, -⟩ := hm
  have hmsg' : (msgAbs C bl m) = some
      { type := .requestVoteRequest, term := uint.Z m.term, source := idAbs m.src, dest := idAbs m.dst,
        lastLogIndex := uint.Z m.index, lastLogTerm := uint.Z m.logterm } := by
    simp only [msgAbs, hty]
  simp only [hmsg', Option.get_some]
  unfold Etcdraft.Line.isRequestVoteRequest
  simp only [msgLine, evConv, hmsg, Option.map_some]
  rw [htyp, hty, hterm, hlt, hidx, gInt_of_lt _ bt, gInt_of_lt _ bi, gInt_of_lt _ blt, gsStr_msgTypeStr_vote]
  simp [Etcdraft.raftMsgType]

/-- A vote request's line's non-receive successors: the specification's `RequestVote(i, j)` of the
line's sender and receiver (pre-vote off), when it matches the line. -/
theorem nonReceive_requestVote (t : Etcdraft.Trace) (ts : Etcdraft.TState) (i j : Etcdraft.ID)
    (s2 : Etcdraft.State) (hl : ts.l ≤ t.len)
    (hname : (t.line ts.l).ev.name = "SendRequestVoteRequest")
    (hfrom : (t.line ts.l).from = i) (hto : (t.line ts.l).to = j) (hsome : (t.line ts.l).ev.msg.isSome = true)
    (hnd : t.server.Nodup) (hi : i ∈ t.server) (hj : j ∈ t.server) (hpv : ts.s.preVote = false)
    (hrv : ts.s.requestVote i j = some s2) (hpost : (t.line ts.l).stateMatches s2 i = true)
    (hnew : Etcdraft.newPending ts.s s2 (fun m => (t.line ts.l).isRequestVoteRequest m ||
      ((t.line ts.l).isRequestVoteResponse m && m.source == m.dest)) = true) :
    t.nonReceive ts = .ok [s2] := by
  have hpre : ts.s.requestPreVote i j = none := by
    unfold Etcdraft.State.requestPreVote; simp [hpv]
  have hf : t.pairs.flatMap (fun p => t.requestVoteIfLogged ts p.1 p.2) = [s2] := by
    apply flatMap_single _ _ (i, j) s2 (pairs_nodup t hnd) ((mem_pairs t i j).2 ⟨hi, hj⟩)
    · simp [Etcdraft.Trace.requestVoteIfLogged, Etcdraft.Trace.isMessageEvent, Etcdraft.Trace.isEvent,
        Etcdraft.Trace.validatePostStates, hl, hname, hfrom, hto, hsome, hrv, hpre, hpost, hnew, Etcdraft.somes]
    · rintro ⟨a, b⟩ _ hne
      have : ¬ (a = i ∧ b = j) := fun h => hne (by rw [h.1, h.2])
      simp only [Etcdraft.Trace.requestVoteIfLogged, Etcdraft.Trace.isMessageEvent, Etcdraft.Trace.isEvent,
        hfrom, hto, hname]
      by_cases ha : a = i
      · have hb : b ≠ j := fun hb => this ⟨ha, hb⟩
        simp [ha, Ne.symm hb]
      · simp [Ne.symm ha]
  unfold Etcdraft.Trace.nonReceive
  simp only [hname, hf]
  simp [Etcdraft.Trace.skipUnusedLogline, Etcdraft.Trace.isEvent, hname,
    Etcdraft.Trace.isBecomeFollowerInUpdateTermOrReturnToFollower, pure, Except.pure, bind, Except.bind]

/-- **A vote request's line's step**: a candidate's `MsgVote` (its last index and term, to a voter it
has no vote of), the specification's `RequestVote(i, j)`; the candidate's server unchanged. -/
theorem simRun_requestVote (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (id : w64) (s : NState) (cfg : CfgM) (m : Msg)
    (hev : SendEvOf (W64 13) id s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : id ∈ C) (hdC : m.dst ∈ C) (hsrv : σ.server = confAbs C) (hpv : σ.preVote = false)
    (hR : SimServerR C C.length (toPState s) (σ.s (idAbs id))) (hs : LogShapeOk C.length (toPState s))
    (hrole : s.role = .candidate) (hty : m.ty = .vote) (hsrc : m.src = id) (hdst : m.dst ≠ id)
    (hw : (toPState s).votes !! m.dst = none) (hterm : m.term = s.term)
    (hidx : m.index = (plogLast (toPState s).base (toPState s).log).index')
    (hlt : m.logterm = (plogLast (toPState s).base (toPState s).log).term')
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (bi : uint.Z m.index < 2 ^ 63)
    (blt : uint.Z m.logterm < 2 ^ 63)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinv : (σ.send ((msgAbs C C.length m).get (by simp [msgAbs, hty]))).violated = .ok none) :
    SimRun C (L ++ [e]) (σ.send ((msgAbs C C.length m).get (by simp [msgAbs, hty]))) := by
  obtain ⟨hname, hnid, hterm', hvote, hcommit', hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  have hname' : gsStr e.name = "SendRequestVoteRequest" := by
    simp only [evtNames] at hname
    have : e.name = go!"SendRequestVoteRequest" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  have htyp : tm.typ = msgTypeStr .vote := by rw [hm.1, hty]
  have hrv := requestVote_send σ C C.length (toPState s) id m hR (by simp [toPState, hrole, proleRole]) hs hty
    hsrc hdst hdC hw (by rw [hterm]; rfl) hidx hlt
  apply simRun_msg C L σ _ hrun hL e id s.vote m.src m.dst xs tm hnid hvote hconf hmsg hm.2.2.1 hm.2.2.2.1
    (by rw [htyp]; rfl) (by rw [hname']; rfl) (by rw [hname']; decide) hboot _ hinv
  intro lines ts hl hts hl'
  have hlen := parseLines_length _ _ hl
  simp only [List.length_map] at hlen
  have hline := linesTrace_line_last C lines (msgLine e id s.vote m.src m.dst xs) ts.l (by omega)
  apply nonReceive_requestVote _ ts (idAbs m.src) (idAbs m.dst) _ (by simp [linesTrace, Etcdraft.Trace.len]; omega)
  · rw [hline]; simp [msgLine, evConv, hname']
  · rw [hline]; rfl
  · rw [hline]; rfl
  · rw [hline]; simp [msgLine, evConv, hmsg]
  · exact confAbs_nodup C
  · simp only [linesTrace]; rw [mem_confAbs, hsrc]; exact hC
  · simp only [linesTrace]; rw [mem_confAbs]; exact hdC
  · rw [hts]; exact hpv
  · rw [hts, hsrc]; exact hrv
  · rw [hline, hsrc]
    have := stateMatches_node C s (σ.s (idAbs id)) e id xs hR hs (by rw [hrole]; decide) hterm' hcommit' hrl
      hlog (hxs.trans hin) bt bc bl σ rfl (by rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC)
    unfold Etcdraft.Line.stateMatches at this ⊢
    simpa [Etcdraft.State.send, msgLine, nodeLine] using this
  · rw [hline, hts]
    apply newPending_send
    have := isRVReq_vote C C.length e id s.vote xs m tm hmsg hm hty (by rw [hterm]; exact bt) bi blt
    rw [hsrc] at this ⊢
    simp [this]

theorem gsStr_msgTypeStr_voteResp : gsStr (msgTypeStr .voteResp) = "MsgVoteResp" := by rfl

/-- **A vote response's line predicate** (`LoglineIsRequestVoteResponse` of its abstraction). -/
theorem isRVResp_voteResp (C : List w64) (bl : Nat) (e : TraceEv) (id vote : w64) (xs : List w64) (m : Msg)
    (tm : TraceMsg) (hmsg : e.msg = some tm) (hm : MsgEvOf m tm) (hty : m.ty = .voteResp)
    (bt : uint.Z m.term < 2 ^ 63) :
    (msgLine e id vote m.src m.dst xs).isRequestVoteResponse
      ((msgAbs C bl m).get (by simp [msgAbs, hty])) = true := by
  obtain ⟨htyp, hterm, -, -, -, -, -, -, hrej⟩ := hm
  have hmsg' : (msgAbs C bl m) = some
      { type := .requestVoteResponse, term := uint.Z m.term, source := idAbs m.src, dest := idAbs m.dst,
        voteGranted := !m.reject } := by
    simp only [msgAbs, hty]
  simp only [hmsg', Option.get_some]
  unfold Etcdraft.Line.isRequestVoteResponse
  simp only [msgLine, evConv, hmsg, Option.map_some]
  rw [htyp, hty, hterm, hrej, gInt_of_lt _ bt, gsStr_msgTypeStr_voteResp]
  simp [Etcdraft.raftMsgType]

/-- A self vote's line's non-receive successors: the specification's `RequestVote(i, i)`. -/
theorem nonReceive_selfVote (t : Etcdraft.Trace) (ts : Etcdraft.TState) (i : Etcdraft.ID)
    (s2 : Etcdraft.State) (hl : ts.l ≤ t.len)
    (hname : (t.line ts.l).ev.name = "SendRequestVoteResponse")
    (hfrom : (t.line ts.l).from = i) (hto : (t.line ts.l).to = i)
    (hself : ∃ em, (t.line ts.l).ev.msg = some em ∧ em.from = em.to)
    (hnd : t.server.Nodup) (hi : i ∈ t.server) (hpv : ts.s.preVote = false)
    (hrv : ts.s.requestVote i i = some s2) (hpost : (t.line ts.l).stateMatches s2 i = true)
    (hnew : Etcdraft.newPending ts.s s2 (fun m => (t.line ts.l).isRequestVoteRequest m ||
      ((t.line ts.l).isRequestVoteResponse m && m.source == m.dest)) = true) :
    t.nonReceive ts = .ok [s2] := by
  obtain ⟨em, hem, heq⟩ := hself
  have hsome : (t.line ts.l).ev.msg.isSome = true := by rw [hem]; rfl
  have hpre : ts.s.requestPreVote i i = none := by
    unfold Etcdraft.State.requestPreVote; simp [hpv]
  have hf : t.pairs.flatMap (fun p => t.requestVoteIfLogged ts p.1 p.2) = [s2] := by
    apply flatMap_single _ _ (i, i) s2 (pairs_nodup t hnd) ((mem_pairs t i i).2 ⟨hi, hi⟩)
    · simp [Etcdraft.Trace.requestVoteIfLogged, Etcdraft.Trace.isMessageEvent, Etcdraft.Trace.isEvent,
        Etcdraft.Trace.validatePostStates, hl, hname, hfrom, hto, hsome, hrv, hpre, hpost, hnew, Etcdraft.somes]
    · rintro ⟨a, b⟩ _ hne
      have : ¬ (a = i ∧ b = i) := fun h => hne (by rw [h.1, h.2])
      simp only [Etcdraft.Trace.requestVoteIfLogged, Etcdraft.Trace.isMessageEvent, Etcdraft.Trace.isEvent,
        hfrom, hto, hname]
      by_cases ha : a = i
      · have hb : b ≠ i := fun hb => this ⟨ha, hb⟩
        simp [ha, Ne.symm hb]
      · simp [Ne.symm ha]
  have hskip : t.skipUnusedLogline ts = false := by
    unfold Etcdraft.Trace.skipUnusedLogline Etcdraft.Trace.isEvent
    simp [hname, hem, heq, Etcdraft.Trace.isBecomeFollowerInUpdateTermOrReturnToFollower, Etcdraft.Trace.isEvent]
  unfold Etcdraft.Trace.nonReceive
  simp only [hname, hf, hskip]
  simp [pure, Except.pure, bind, Except.bind]

/-- **A candidate's self vote's line's step**: `campaign`'s `MsgVoteResp` to itself, the
specification's `RequestVote(i, i)`. -/
theorem simRun_selfVote (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (id : w64) (s : NState) (cfg : CfgM) (m : Msg)
    (hev : SendEvOf (W64 15) id s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : id ∈ C) (hsrv : σ.server = confAbs C) (hpv : σ.preVote = false)
    (hR : SimServerR C C.length (toPState s) (σ.s (idAbs id))) (hs : LogShapeOk C.length (toPState s))
    (hrole : s.role = .candidate) (hty : m.ty = .voteResp) (hsrc : m.src = id) (hdst : m.dst = id)
    (hw : (toPState s).votes !! id = none) (hterm : m.term = s.term) (hrej : m.reject = false)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinv : (σ.send ((msgAbs C C.length m).get (by simp [msgAbs, hty]))).violated = .ok none) :
    SimRun C (L ++ [e]) (σ.send ((msgAbs C C.length m).get (by simp [msgAbs, hty]))) := by
  obtain ⟨hname, hnid, hterm', hvote, hcommit', hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  have hname' : gsStr e.name = "SendRequestVoteResponse" := by
    simp only [evtNames] at hname
    have : e.name = go!"SendRequestVoteResponse" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  have htyp : tm.typ = msgTypeStr .voteResp := by rw [hm.1, hty]
  have hrv := requestVoteSelf_send σ C C.length (toPState s) id m hR (by simp [toPState, hrole, proleRole]) hty
    hsrc hdst hC hw (by rw [hterm]; rfl) hrej
  apply simRun_msg C L σ _ hrun hL e id s.vote m.src m.dst xs tm hnid hvote hconf hmsg hm.2.2.1 hm.2.2.2.1
    (by rw [htyp]; rfl) (by rw [hname']; rfl) (by rw [hname']; decide) hboot _ hinv
  intro lines ts hl hts hl'
  have hlen := parseLines_length _ _ hl
  simp only [List.length_map] at hlen
  have hline := linesTrace_line_last C lines (msgLine e id s.vote m.src m.dst xs) ts.l (by omega)
  apply nonReceive_selfVote _ ts (idAbs id) _ (by simp [linesTrace, Etcdraft.Trace.len]; omega)
  · rw [hline]; simp [msgLine, evConv, hname']
  · rw [hline, hsrc]; rfl
  · rw [hline, hdst]; rfl
  · rw [hline]
    refine ⟨_, by simp [msgLine, evConv, hmsg]; rfl, ?_⟩
    simp only [hm.2.2.1, hm.2.2.2.1, hsrc, hdst]
  · exact confAbs_nodup C
  · simp only [linesTrace]; rw [mem_confAbs]; exact hC
  · rw [hts]; exact hpv
  · rw [hts]; exact hrv
  · rw [hline]
    have := stateMatches_node C s (σ.s (idAbs id)) e id xs hR hs (by rw [hrole]; decide) hterm' hcommit' hrl
      hlog (hxs.trans hin) bt bc bl σ rfl (by rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC)
    unfold Etcdraft.Line.stateMatches at this ⊢
    simpa [Etcdraft.State.send, msgLine, nodeLine] using this
  · rw [hline, hts]
    apply newPending_send
    have := isRVResp_voteResp C C.length e id s.vote xs m tm hmsg hm hty (by rw [hterm]; exact bt)
    have hsd : ((msgAbs C C.length m).get (by simp [msgAbs, hty])).source =
        ((msgAbs C C.length m).get (by simp [msgAbs, hty])).dest := by
      simp [msgAbs, hty, hsrc, hdst]
    simp [this, hsd]

theorem gsStr_msgTypeStr_appResp : gsStr (msgTypeStr .appResp) = "MsgAppResp" := by rfl

/-- **An accepting append response's line predicate** (`LoglineIsAppendEntriesResponse`). -/
theorem isAEResp_appResp (C : List w64) (bl : Nat) (e : TraceEv) (id vote : w64) (xs : List w64) (m : Msg)
    (tm : TraceMsg) (hmsg : e.msg = some tm) (hm : MsgEvOf m tm) (hty : m.ty = .appResp) (hrej : m.reject = false)
    (bt : uint.Z m.term < 2 ^ 63) (bi : uint.Z m.index < 2 ^ 63) :
    (msgLine e id vote m.src m.dst xs).isAppendEntriesResponse
      ((msgAbs C bl m).get (by simp [msgAbs, hty])) = true := by
  obtain ⟨htyp, hterm, -, -, -, -, hidx, -, hrej'⟩ := hm
  have hmsg' : (msgAbs C bl m) = some
      { type := .appendEntriesResponse, subtype := "app", term := uint.Z m.term, success := true,
        matchIndex := uint.Z m.index, source := idAbs m.src, dest := idAbs m.dst } := by
    simp [msgAbs, hty, hrej]
  simp only [hmsg', Option.get_some]
  unfold Etcdraft.Line.isAppendEntriesResponse
  simp only [msgLine, evConv, hmsg, Option.map_some]
  rw [htyp, hty, hterm, hidx, hrej', hrej, gInt_of_lt _ bt, gInt_of_lt _ bi, gsStr_msgTypeStr_appResp]
  simp [Etcdraft.raftMsgType, Etcdraft.raftMsgSubtype]

/-- A self acknowledgement's line's non-receive successors: the specification's
`AppendEntriesToSelf(i)`. -/
theorem nonReceive_selfAck (t : Etcdraft.Trace) (ts : Etcdraft.TState) (i : Etcdraft.ID)
    (s2 : Etcdraft.State) (hl : ts.l ≤ t.len)
    (hname : (t.line ts.l).ev.name = "SendAppendEntriesResponse")
    (hfrom : (t.line ts.l).from = i) (hto : (t.line ts.l).to = i)
    (hself : ∃ em, (t.line ts.l).ev.msg = some em ∧ em.from = em.to)
    (hnd : t.server.Nodup) (hi : i ∈ t.server)
    (hae : ts.s.appendEntriesToSelf i = some s2) (hpost : (t.line ts.l).stateMatches s2 i = true)
    (hnew : Etcdraft.newPending ts.s s2 (fun m => (t.line ts.l).isAppendEntriesResponse m && m.source == m.dest) = true) :
    t.nonReceive ts = .ok [s2] := by
  obtain ⟨em, hem, heq⟩ := hself
  have hsome : (t.line ts.l).ev.msg.isSome = true := by rw [hem]; rfl
  have hf : t.server.flatMap (t.appendEntriesToSelfIfLogged ts) = [s2] := by
    apply flatMap_single _ _ i s2 hnd hi
    · simp [Etcdraft.Trace.appendEntriesToSelfIfLogged, Etcdraft.Trace.isMessageEvent, Etcdraft.Trace.isEvent,
        Etcdraft.Trace.validatePostStates, hl, hname, hfrom, hto, hsome, hae, hpost, hnew]
    · intro j _ hj
      simp [Etcdraft.Trace.appendEntriesToSelfIfLogged, Etcdraft.Trace.isMessageEvent, Etcdraft.Trace.isEvent,
        hfrom, Ne.symm hj]
  have hskip : t.skipUnusedLogline ts = false := by
    unfold Etcdraft.Trace.skipUnusedLogline Etcdraft.Trace.isEvent
    simp [hname, hem, heq, Etcdraft.Trace.isBecomeFollowerInUpdateTermOrReturnToFollower, Etcdraft.Trace.isEvent]
  unfold Etcdraft.Trace.nonReceive
  simp only [hname, hf, hskip]
  simp [pure, Except.pure, bind, Except.bind]

/-- **A leader's self acknowledgement's line's step** (`appendEntry`'s `MsgAppResp` to itself at
its last index): the specification's `AppendEntriesToSelf(i)`. -/
theorem simRun_selfAck (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (id : w64) (s : NState) (cfg : CfgM)
    (hev : SendEvOf (W64 11) id s cfg (pselfAck id (toPState s)) e) (hin : (elements cfg.incoming).Perm C)
    (hout : cfg.outgoing = ∅) (hC : id ∈ C) (hsrv : σ.server = confAbs C)
    (hR : SimServerR C C.length (toPState s) (σ.s (idAbs id))) (hs : LogShapeOk C.length (toPState s))
    (hrole : s.role = .leader)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinv : (σ.send ((msgAbs C C.length (pselfAck id (toPState s))).get
      (by simp [msgAbs, pselfAck]))).violated = .ok none) :
    SimRun C (L ++ [e]) (σ.send ((msgAbs C C.length (pselfAck id (toPState s))).get
      (by simp [msgAbs, pselfAck]))) := by
  obtain ⟨hname, hnid, hterm', hvote, hcommit', hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  have hname' : gsStr e.name = "SendAppendEntriesResponse" := by
    simp only [evtNames] at hname
    have : e.name = go!"SendAppendEntriesResponse" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  have htyp : tm.typ = msgTypeStr .appResp := by rw [hm.1]; rfl
  have hae := appendEntriesToSelf_send σ C C.length (toPState s) id hR (by simp [toPState, hrole, proleRole]) hs
  apply simRun_msg C L σ _ hrun hL e id s.vote id id xs tm hnid hvote hconf hmsg hm.2.2.1 hm.2.2.2.1
    (by rw [htyp]; rfl) (by rw [hname']; rfl) (by rw [hname']; decide) hboot _ hinv
  intro lines ts hl hts hl'
  have hlen := parseLines_length _ _ hl
  simp only [List.length_map] at hlen
  have hline := linesTrace_line_last C lines (msgLine e id s.vote id id xs) ts.l (by omega)
  apply nonReceive_selfAck _ ts (idAbs id) _ (by simp [linesTrace, Etcdraft.Trace.len]; omega)
  · rw [hline]; simp [msgLine, evConv, hname']
  · rw [hline]; rfl
  · rw [hline]; rfl
  · rw [hline]
    refine ⟨_, by simp [msgLine, evConv, hmsg]; rfl, ?_⟩
    simp only [hm.2.2.1, hm.2.2.2.1]; rfl
  · exact confAbs_nodup C
  · simp only [linesTrace]; rw [mem_confAbs]; exact hC
  · rw [hts]; exact hae
  · rw [hline]
    have := stateMatches_node C s (σ.s (idAbs id)) e id xs hR hs (by rw [hrole]; decide) hterm' hcommit' hrl
      hlog (hxs.trans hin) bt bc bl σ rfl (by rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC)
    unfold Etcdraft.Line.stateMatches at this ⊢
    simpa [Etcdraft.State.send, msgLine, nodeLine] using this
  · rw [hline, hts]
    apply newPending_send
    have := isAEResp_appResp C C.length e id s.vote xs (pselfAck id (toPState s)) tm hmsg hm rfl rfl
      (by simp [pselfAck, toPState]; exact bt) (by simpa [pselfAck] using bl)
    simp only [msgAbs, pselfAck, Option.get_some] at this
    simp only [msgAbs, pselfAck, Option.get_some, Bool.and_eq_true, beq_self_eq_true, and_true]
    exact this

/-- A monadic fold appending each element's results is the concatenation. -/
theorem foldlM_concat {α β ε : Type} (F : List β → α → Except ε (List β)) (r : α → List β) :
    ∀ (l : List α) (acc : List β), (∀ acc, ∀ x ∈ l, F acc x = .ok (acc ++ r x)) →
      l.foldlM F acc = .ok (acc ++ l.flatMap r) := by
  intro l
  induction l with
  | nil => intro acc _; simp [pure, Except.pure]
  | cons x l ih =>
    intro acc h
    rw [List.foldlM_cons, h acc x (by simp)]
    simp only [bind, Except.bind]
    rw [ih _ (fun acc y hy => h acc y (by simp [hy]))]
    simp

theorem intRange_nodup (lo hi : Int) : (Etcdraft.intRange lo hi).Nodup := by
  unfold Etcdraft.intRange
  exact List.nodup_range.map (f := fun (k : Nat) => lo + (k : Int)) (fun _ _ h e => h (by omega))

theorem mem_intRange (lo hi x : Int) (h1 : lo ≤ x) (h2 : x ≤ hi) : x ∈ Etcdraft.intRange lo hi := by
  unfold Etcdraft.intRange
  rw [List.mem_map]
  exact ⟨(x - lo).toNat, by rw [List.mem_range]; omega, by omega⟩

/-- A `MsgApp` line's non-receive successors: the specification's `AppendEntries(i, j, <<b, e>>)`
of the line's sender, receiver and range (`b` the line's index plus 1, `e` past its entries,
within the range `TraceNext` tries: past the receiver's `matchIndex`, at most one past the log). -/
theorem nonReceive_msgApp (t : Etcdraft.Trace) (ts : Etcdraft.TState) (i j : Etcdraft.ID)
    (s2 : Etcdraft.State) (em : Etcdraft.EventMsg) (hl : ts.l ≤ t.len)
    (hname : (t.line ts.l).ev.name = "SendAppendEntriesRequest")
    (hfrom : (t.line ts.l).from = i) (hto : (t.line ts.l).to = j)
    (hem : (t.line ts.l).ev.msg = some em) (hty : em.type = "MsgApp")
    (hnd : t.server.Nodup) (hi : i ∈ t.server) (hj : j ∈ t.server)
    (hlo : (ts.s.s i).matchIndex j + 1 ≤ em.index + 1)
    (hhi : em.index + 1 + em.entries ≤ ((ts.s.s i).log.length : Int) + 1)
    (hb0 : (ts.s.s i).matchIndex j + 1 ≤ em.index + 1 + em.entries) (hent0 : 0 ≤ em.entries)
    (hae : ts.s.appendEntries i j (em.index + 1) (em.index + 1 + em.entries) = .ok (some s2))
    (hv : t.validateAfterAppendEntries ts s2 i = true) :
    t.nonReceive ts = .ok [s2] := by
  -- each `AppendEntriesIfLogged` gives `[s2]` at the line's sender, receiver and range, else nothing
  have hR : ∀ (p : Etcdraft.ID × Etcdraft.ID) (b e : Int), t.appendEntriesIfLogged ts p.1 p.2 b e =
      .ok (if p = (i, j) ∧ b = em.index + 1 ∧ e = em.index + 1 + em.entries then [s2] else []) := by
    rintro ⟨a, c⟩ b e
    unfold Etcdraft.Trace.appendEntriesIfLogged
    by_cases hp : a = i ∧ c = j
    · obtain ⟨rfl, rfl⟩ := hp
      have hme : t.isMessageEvent ts "SendAppendEntriesRequest" a c = true := by
        simp [Etcdraft.Trace.isMessageEvent, Etcdraft.Trace.isEvent, hl, hname, hfrom, hto, hem]
      simp only [hme, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hem]
      by_cases hbe : b = em.index + 1 ∧ e = em.index + 1 + em.entries
      · obtain ⟨rfl, rfl⟩ := hbe
        simp [hty, hae, hv, bind, Except.bind, pure, Except.pure]
      · have : (em.type == "MsgApp" && b == em.index + 1 && e == b + em.entries) = false := by
          simp only [hty, beq_self_eq_true, Bool.true_and, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
          by_cases hb : b = em.index + 1
          · right; intro he; exact hbe ⟨hb, by rw [he, hb]⟩
          · left; exact hb
        simp [this, hbe, pure, Except.pure]
    · have hme : t.isMessageEvent ts "SendAppendEntriesRequest" a c = false := by
        simp only [Etcdraft.Trace.isMessageEvent, hfrom, hto]
        by_cases ha : a = i
        · have hc : c ≠ j := fun hc => hp ⟨ha, hc⟩
          simp [ha, Ne.symm hc]
        · simp [Ne.symm ha]
      have hne : ¬ ((a, c) = (i, j) ∧ b = em.index + 1 ∧ e = em.index + 1 + em.entries) := by
        rintro ⟨h, -⟩; simp only [Prod.mk.injEq] at h; exact hp h
      simp only [hme, Bool.not_false, ↓reduceIte, hne]; rfl
  have hfold : t.pairs.foldlM (fun acc p => do
        let lo := (ts.s.s p.1).matchIndex p.2 + 1
        let hi := ((ts.s.s p.1).log.length : Int) + 1
        (Etcdraft.intRange lo hi).foldlM (fun acc b =>
          (Etcdraft.intRange lo hi).foldlM (fun acc e => do
            return acc ++ (← t.appendEntriesIfLogged ts p.1 p.2 b e)) acc) acc) [] = .ok [s2] := by
    rw [foldlM_concat _ (fun p => (Etcdraft.intRange ((ts.s.s p.1).matchIndex p.2 + 1)
        (((ts.s.s p.1).log.length : Int) + 1)).flatMap (fun b =>
          (Etcdraft.intRange ((ts.s.s p.1).matchIndex p.2 + 1) (((ts.s.s p.1).log.length : Int) + 1)).flatMap
            (fun e => if p = (i, j) ∧ b = em.index + 1 ∧ e = em.index + 1 + em.entries then [s2] else [])))]
    · simp only [List.nil_append]
      congr 1
      apply flatMap_single _ _ (i, j) s2 (pairs_nodup t hnd) ((mem_pairs t i j).2 ⟨hi, hj⟩)
      · apply flatMap_single _ _ (em.index + 1) s2 (intRange_nodup _ _) (mem_intRange _ _ _ hlo (by simp only; omega))
        · apply flatMap_single _ _ (em.index + 1 + em.entries) s2 (intRange_nodup _ _)
            (mem_intRange _ _ _ hb0 hhi)
          · simp
          · intro x _ hx; simp [hx]
        · intro x _ hx; rw [List.flatMap_eq_nil_iff]; intro y _; simp [hx]
      · intro x _ hx; rw [List.flatMap_eq_nil_iff]; intro y _; rw [List.flatMap_eq_nil_iff]; intro z _
        simp [hx]
    · intro acc p _
      simp only
      rw [foldlM_concat _ (fun b => (Etcdraft.intRange ((ts.s.s p.1).matchIndex p.2 + 1)
          (((ts.s.s p.1).log.length : Int) + 1)).flatMap
            (fun e => if p = (i, j) ∧ b = em.index + 1 ∧ e = em.index + 1 + em.entries then [s2] else []))]
      intro acc' b _
      rw [foldlM_concat _ (fun e => if p = (i, j) ∧ b = em.index + 1 ∧ e = em.index + 1 + em.entries then [s2] else [])]
      intro acc'' e _
      simp [hR, bind, Except.bind, pure, Except.pure]
  unfold Etcdraft.Trace.nonReceive
  have hmt : (t.line ts.l).ev.msg.map Etcdraft.EventMsg.type = some "MsgApp" := by rw [hem, Option.map_some, hty]
  simp only [hname, hmt]
  simp only [bind, Except.bind] at hfold ⊢
  rw [hfold]
  simp [Etcdraft.Trace.skipUnusedLogline, Etcdraft.Trace.isEvent, hname,
    Etcdraft.Trace.isBecomeFollowerInUpdateTermOrReturnToFollower, pure, Except.pure]

theorem gsStr_msgTypeStr_app : gsStr (msgTypeStr .app) = "MsgApp" := by rfl

/-- **A `MsgApp`'s line predicate** (`LoglineIsAppendEntriesRequest` of its abstraction). -/
theorem isAER_app (C : List w64) (bl : Nat) (e : TraceEv) (id vote : w64) (xs : List w64) (m : Msg)
    (tm : TraceMsg) (hmsg : e.msg = some tm) (hm : MsgEvOf m tm) (hty : m.ty = .app)
    (bt : uint.Z m.term < 2 ^ 63) (bc : uint.Z m.commit < 2 ^ 63) (bi : uint.Z m.index < 2 ^ 63)
    (blt : uint.Z m.logterm < 2 ^ 63) (bk : m.entries.length < 2 ^ 63) :
    (msgLine e id vote m.src m.dst xs).isAppendEntriesRequest
      ((msgAbs C bl m).get (by simp [msgAbs, hty])) = true := by
  obtain ⟨htyp, hterm, -, -, hent, hlt, hidx, hcommit, -⟩ := hm
  simp only [msgAbs, hty, Option.get_some]
  unfold Etcdraft.Line.isAppendEntriesRequest
  simp only [msgLine, evConv, hmsg, Option.map_some]
  rw [htyp, hty, hterm, hcommit, hent, hlt, hidx, gInt_of_lt _ bt, gInt_of_lt _ bc, gInt_of_lt _ bi,
    gInt_of_lt _ blt, gsStr_msgTypeStr_app, logAbs_length]
  have hk : gInt (W64 m.entries.length) = (m.entries.length : Int) := by
    rw [gInt_of_lt _ (by word)]; word
  rw [hk]
  simp [Etcdraft.raftMsgType, Etcdraft.raftMsgSubtype]

/-- **A `MsgApp` line's step**: a leader's append request (the entries after its index, the term
there, its commit index; past the receiver's `Match`), the specification's
`AppendEntries(i, j, <<index + 1, index + 1 + |entries|>>)`; the leader's server unchanged. -/
theorem simRun_msgApp (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (id : w64) (s : NState) (cfg : CfgM) (m : Msg)
    (hev : SendEvOf (W64 9) id s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : id ∈ C) (hdC : m.dst ∈ C) (hsrv : σ.server = confAbs C)
    (hR : SimServerR C C.length (toPState s) (σ.s (idAbs id))) (hs : LogShapeOk C.length (toPState s))
    (hrole : s.role = .leader) (hty : m.ty = .app) (hsrc : m.src = id) (hdst : m.dst ≠ id)
    (hterm : m.term = s.term) (hpk : uint.nat m.index + m.entries.length ≤ (toPState s).log.length)
    (hlt : plogTermAt (toPState s).base (toPState s).log m.index = some m.logterm)
    (hents : m.entries = ((toPState s).log.drop (uint.nat m.index)).take m.entries.length)
    (hcommit : m.commit = (toPState s).commit)
    (hmatch : uint.Z (matchOf (toPState s) m.dst) ≤ uint.Z m.index)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (bi : uint.Z m.index < 2 ^ 63)
    (blt : uint.Z m.logterm < 2 ^ 63)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinv : (σ.send ((msgAbs C C.length m).get (by simp [msgAbs, hty]))).violated = .ok none) :
    SimRun C (L ++ [e]) (σ.send ((msgAbs C C.length m).get (by simp [msgAbs, hty]))) := by
  obtain ⟨hname, hnid, hterm', hvote, hcommit', hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  have hname' : gsStr e.name = "SendAppendEntriesRequest" := by
    simp only [evtNames] at hname
    have : e.name = go!"SendAppendEntriesRequest" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  have htyp : tm.typ = msgTypeStr .app := by rw [hm.1, hty]
  have hlen64 : (toPState s).log.length < 2 ^ 63 := by
    have := plastIndex_length _ _ hs; omega
  have hae := appendEntries_send σ C C.length (toPState s) id m m.entries.length hR
    (by simp [toPState, hrole, proleRole]) hs hty hsrc hdst hdC (by rw [hterm]; rfl) hpk hlt hents hcommit
  have hidxZ : ((uint.nat m.index : Nat) : Int) = uint.Z m.index := by word
  have hk : gInt (W64 m.entries.length) = (m.entries.length : Int) := by
    rw [gInt_of_lt _ (by word)]; word
  apply simRun_msg C L σ _ hrun hL e id s.vote m.src m.dst xs tm hnid hvote hconf hmsg hm.2.2.1 hm.2.2.2.1
    (by rw [htyp]; rfl) (by rw [hname']; rfl) (by rw [hname']; decide) hboot _ hinv
  intro lines ts hl hts hl'
  have hlen := parseLines_length _ _ hl
  simp only [List.length_map] at hlen
  have hline := linesTrace_line_last C lines (msgLine e id s.vote m.src m.dst xs) ts.l (by omega)
  subst hts
  have hR6 := hR.2.2.2.2.2.1
  have hR11 := hR.2.2.2.2.2.2.2.2.2.2
  cases hc : (msgLine e id s.vote m.src m.dst xs).ev.msg with
  | none => simp [msgLine, evConv, hmsg] at hc
  | some em =>
    have hety : em.type = "MsgApp" := by
      have : em.type = gsStr tm.typ := by simp [msgLine, evConv, hmsg] at hc; rw [← hc]
      rw [this, htyp]; rfl
    have heidx : em.index = uint.Z m.index := by
      have : em.index = gInt tm.index := by simp [msgLine, evConv, hmsg] at hc; rw [← hc]
      rw [this, hm.2.2.2.2.2.2.1, gInt_of_lt _ bi]
    have heent : em.entries = (m.entries.length : Int) := by
      have : em.entries = gInt tm.entries := by simp [msgLine, evConv, hmsg] at hc; rw [← hc]
      rw [this, hm.2.2.2.2.1, hk]
    have hmi : (ts.s.s (idAbs id)).matchIndex (idAbs m.dst) = uint.Z (matchOf (toPState s) m.dst) :=
      hR11 (by simp [toPState, hrole, proleRole]) m.dst hdC
    have hll : ((ts.s.s (idAbs id)).log.length : Int) = (toPState s).log.length := by rw [hR6, logAbs_length]
    apply nonReceive_msgApp _ ts (idAbs id) (idAbs m.dst) _ em (by simp [linesTrace, Etcdraft.Trace.len]; omega)
    · rw [hline]; simp [msgLine, evConv, hname']
    · rw [hline]; show idAbs m.src = idAbs id; rw [hsrc]
    · rw [hline]; rfl
    · rw [hline]; exact hc
    · exact hety
    · exact confAbs_nodup C
    · simp only [linesTrace]; rw [mem_confAbs]; exact hC
    · simp only [linesTrace]; rw [mem_confAbs]; exact hdC
    · rw [hmi, heidx]; omega
    · rw [heidx, heent, hll]; omega
    · rw [hmi, heidx, heent]; omega
    · rw [heent]; omega
    · rw [heidx, heent, ← hidxZ]; exact hae
    · unfold Etcdraft.Trace.validateAfterAppendEntries Etcdraft.Trace.validatePostStates
      rw [hline, Bool.and_eq_true]
      constructor
      · have := stateMatches_node C s (ts.s.s (idAbs id)) e id xs hR
          hs (by rw [hrole]; decide) hterm' hcommit' hrl hlog (hxs.trans hin) bt bc bl ts.s rfl
          (by rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC)
        unfold Etcdraft.Line.stateMatches at this ⊢
        simpa [Etcdraft.State.send, msgLine, nodeLine] using this
      · apply newPending_send
        have := isAER_app C C.length e id s.vote xs m tm hmsg hm hty (by rw [hterm]; exact bt)
          (by rw [hcommit]; simpa [toPState] using bc) bi blt (by omega)
        rw [hsrc] at this ⊢
        exact this

/-! ### Receive lines -/

/-- The message predicate a receive line applies (`receive`'s `isMatch`). -/
def recvPred (ln : Etcdraft.Line) (m : Etcdraft.Msg) : Bool :=
  if (or (ln.ev.name == "ReceiveAppendEntriesRequest") (ln.ev.name == "ReceiveSnapshot")) = true then
    ln.isAppendEntriesRequest m
  else if (ln.ev.name == "ReceiveAppendEntriesResponse") = true then ln.isAppendEntriesResponse m
  else if (ln.ev.name == "ReceiveRequestVoteRequest") = true then ln.isRequestVoteRequest m
  else ln.isRequestVoteResponse m

/-- A receive's successor state: on the next line once the message is consumed. -/
def recvNext (ts : Etcdraft.TState) (s2 : Etcdraft.State) (m : Etcdraft.Msg) : Etcdraft.TState :=
  if Etcdraft.oneLessMessage ts.s s2 m then { s := s2, l := ts.l + 1, pl := ts.l }
  else { s := s2, l := ts.l, pl := ts.l }

/-- `receive`, with its predicate `recvPred` and successor `recvNext`. -/
theorem receive_eq (t : Etcdraft.Trace) (ts : Etcdraft.TState) :
    t.receive ts = (if !Etcdraft.isReceiveName (t.line ts.l).ev.name then pure [] else
      ts.s.messages.domain.foldlM (fun acc m =>
        if (or (!recvPred (t.line ts.l) m) (!t.validatePreStates ts m.dest)) = true then pure acc
        else do
          let succ ← ts.s.receive m
          pure (acc ++ succ.map (fun s2 => recvNext ts s2 m))) []) := by
  unfold Etcdraft.Trace.receive
  simp only [bind, pure]
  split <;> rfl

/-- **A receive line's successors from one state**: the one message of the network the line
matches (validated before its first round), received with one successor `s2`. -/
theorem next_receive (t : Etcdraft.Trace) (ts : Etcdraft.TState) (m : Etcdraft.Msg) (s2 : Etcdraft.State)
    (hl0 : ts.l ≠ 0) (hl : ts.l ≤ t.len) (hb : t.bootstrap.getD (ts.l - 1) false = false)
    (hrecv : Etcdraft.isReceiveName (t.line ts.l).ev.name = true)
    (hnd : ts.s.messages.domain.Nodup) (hm : m ∈ ts.s.messages.domain)
    (hmatch : recvPred (t.line ts.l) m = true) (hpre : t.validatePreStates ts m.dest = true)
    (huniq : ∀ m' ∈ ts.s.messages.domain, m' ≠ m →
      (recvPred (t.line ts.l) m' && t.validatePreStates ts m'.dest) = false)
    (hrcv : ts.s.receive m = .ok [s2]) :
    t.next ts = .ok [recvNext ts s2 m] := by
  -- the non-receive successors: none (a receive name is no other action's)
  have hnr : t.nonReceive ts = .ok [] := by
    have hskip : t.skipUnusedLogline ts = false := by
      unfold Etcdraft.Trace.skipUnusedLogline Etcdraft.Trace.isEvent
      unfold Etcdraft.isReceiveName at hrecv
      simp only [Bool.or_eq_true, beq_iff_eq] at hrecv
      rcases hrecv with (((h | h) | h) | h) | h <;>
        simp [h, Etcdraft.Trace.isBecomeFollowerInUpdateTermOrReturnToFollower, Etcdraft.Trace.isEvent]
    unfold Etcdraft.Trace.nonReceive
    unfold Etcdraft.isReceiveName at hrecv
    simp only [Bool.or_eq_true, beq_iff_eq] at hrecv
    rcases hrecv with (((h | h) | h) | h) | h <;> simp [h, hskip, pure, Except.pure, bind, Except.bind]
  -- the receive successors: the one matching message's
  have hrv : t.receive ts = .ok [recvNext ts s2 m] := by
    rw [receive_eq]
    simp only [hrecv, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [foldlM_concat _ (fun m' => if m' = m then [recvNext ts s2 m] else [])]
    · simp only [List.nil_append]
      congr 1
      apply flatMap_single _ _ m _ hnd hm (by simp)
      intro m' _ hne; simp [hne]
    · intro acc m' hm'
      by_cases he : m' = m
      · subst he
        simp [hmatch, hpre, hrcv, bind, Except.bind, pure, Except.pure]
      · have hu := huniq m' hm' he
        rw [Bool.and_eq_false_iff] at hu
        rcases hu with hu | hu <;> simp [hu, he, pure, Except.pure]
  have h1 : (decide (ts.l > t.len) || ts.l == 0) = false := by simp; omega
  unfold Etcdraft.Trace.next
  simp only [h1, hb, Bool.false_eq_true, ↓reduceIte]
  simp [hnr, hrv, bind, Except.bind, pure, Except.pure]

/-- A message line depends on its voters only as a set. -/
theorem msgLine_perm (e : TraceEv) (id vote f d : w64) (xs ys : List w64) (h : xs.Perm ys) :
    msgLine e id vote f d xs = msgLine e id vote f d ys := by
  unfold msgLine
  have : Etcdraft.SetIds.mk (xs.map idAbs) = Etcdraft.SetIds.mk (ys.map idAbs) := by
    apply setIds_mk_eq; intro x; exact (h.map idAbs).mem_iff
  rw [this]

/-- **A successful append response's receive line's step** (at the leader, of its term:
`HandleAppendEntriesResponse`, one round): from a run reaching `σ`, raft's `ReceiveAppendEntriesResponse`
of `m` (its state `s` at `Step`'s entry, `R`-related to its server), `msgAbs m` the one message of
the network the line matches, the invariants at the result. -/
theorem simRun_recvAppResp (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (id : w64) (s : NState) (cfg : CfgM) (m : Msg)
    (hev : SendEvOf (W64 12) id s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : id ∈ C) (hsrv : σ.server = confAbs C)
    (hR : SimServerR C C.length (toPState s) (σ.s (idAbs id))) (hs : LogShapeOk C.length (toPState s))
    (hrole : s.role = .leader) (hty : m.ty = .appResp) (hdst : m.dst = id) (hrej : m.reject = false)
    (hterm : m.term = s.term)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (bi : uint.Z m.index < 2 ^ 63)
    (hnd : σ.messages.domain.Nodup)
    (hmem : (msgAbs C C.length m).get (by simp [msgAbs, hty]) ∈ σ.messages.domain)
    (hcnt : 0 < Etcdraft.Bag.count σ.messages ((msgAbs C C.length m).get (by simp [msgAbs, hty])))
    (huniq : ∀ lines (ts : Etcdraft.TState), ts.s = σ → ∀ m' ∈ σ.messages.domain,
      m' ≠ (msgAbs C C.length m).get (by simp [msgAbs, hty]) →
      (recvPred (msgLine e id s.vote m.src m.dst ((elements cfg.incoming))) m' &&
        (linesTrace C (lines ++ [msgLine e id s.vote m.src m.dst (elements cfg.incoming)])).validatePreStates ts
          m'.dest) = false)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinv : ((withMatch σ (idAbs id) (idAbs m.src) (uint.Z m.index)).discard
      ((msgAbs C C.length m).get (by simp [msgAbs, hty]))).violated = .ok none) :
    SimRun C (L ++ [e]) ((withMatch σ (idAbs id) (idAbs m.src) (uint.Z m.index)).discard
      ((msgAbs C C.length m).get (by simp [msgAbs, hty]))) := by
  obtain ⟨hname, hnid, hterm', hvote, hcommit', hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  have hname' : gsStr e.name = "ReceiveAppendEntriesResponse" := by
    simp only [evtNames] at hname
    have : e.name = go!"ReceiveAppendEntriesResponse" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  have htyp : tm.typ = msgTypeStr .appResp := by rw [hm.1, hty]
  have hparse : Etcdraft.parseLine L.length (evConv e) = .ok (msgLine e id s.vote m.src m.dst (elements cfg.incoming)) := by
    rw [← msgLine_perm e id s.vote m.src m.dst xs _ hxs]
    exact parseLine_msg L.length e id s.vote m.src m.dst xs [] tm hnid hvote hconf hmsg hm.2.2.1 hm.2.2.2.1
      (by rw [htyp]; rfl) (by rw [hname']; decide)
  generalize hmabs : (msgAbs C C.length m).get (by simp [msgAbs, hty]) = mabs at *
  have hmt : mabs.type = .appendEntriesResponse := by rw [← hmabs]; simp [msgAbs, hty, hrej]
  have hmterm : mabs.term = uint.Z m.term := by rw [← hmabs]; simp [msgAbs, hty, hrej]
  have hmsucc : mabs.success = true := by rw [← hmabs]; simp [msgAbs, hty, hrej]
  have hmmi : mabs.matchIndex = uint.Z m.index := by rw [← hmabs]; simp [msgAbs, hty, hrej]
  have hmsrc : mabs.source = idAbs m.src := by rw [← hmabs]; simp [msgAbs, hty, hrej]
  have hmdst : mabs.dest = idAbs m.dst := by rw [← hmabs]; simp [msgAbs, hty, hrej]
  apply simRun_snoc_chain C L σ _ e _ hrun hL hparse
  intro lines ts hl hts hl'
  have hlen := parseLines_length _ _ hl
  simp only [List.length_map] at hlen
  have hline := linesTrace_line_last C lines (msgLine e id s.vote m.src m.dst (elements cfg.incoming)) ts.l (by omega)
  have hcontains : σ.server.contains (idAbs id) = true := by
    rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  have hrcv : ts.s.receive mabs = .ok [(withMatch σ (idAbs id) (idAbs m.src) (uint.Z m.index)).discard mabs] := by
    rw [hts]
    have := receive_appResp σ mabs (by rw [hmdst, hdst]; exact hcontains) hmt
      (by rw [hmdst, hdst, hR.1, hmterm, hterm]; rfl) hmsucc
    rw [this, hmdst, hmsrc, hmmi, hdst]
  have hone : Etcdraft.oneLessMessage ts.s ((withMatch σ (idAbs id) (idAbs m.src) (uint.Z m.index)).discard mabs)
      mabs = true := by
    rw [hts]; exact oneLess_discard σ _ mabs rfl hnd hcnt
  generalize hS : (withMatch σ (idAbs id) (idAbs m.src) (uint.Z m.index)).discard mabs = S at hrcv hone hinv ⊢
  have hrn : recvNext ts S mabs = { s := S, l := ts.l + 1, pl := ts.l } := by simp [recvNext, hone]
  refine ⟨{ s := S, l := ts.l + 1, pl := ts.l }, rfl, Chain.last _ ts _ ?_ rfl hinv⟩
  · have := next_receive (linesTrace C (lines ++ [msgLine e id s.vote m.src m.dst (elements cfg.incoming)])) ts mabs S (by omega) (by simp [linesTrace, Etcdraft.Trace.len]; omega)
      (by simp only [linesTrace]; rw [hl']; simpa using hboot lines _ hl)
      (by rw [hline]; simp [msgLine, evConv, hname']; rfl) (by rw [hts]; exact hnd) (by rw [hts]; exact hmem)
      ?_ ?_ (fun m' hm' hne => by rw [hts] at hm'; rw [hline]; exact huniq lines ts hts m' hm' hne) hrcv
    · rw [this, hrn]
    · rw [hline]
      unfold recvPred
      have hn1 : (or ((msgLine e id s.vote m.src m.dst (elements cfg.incoming)).ev.name == "ReceiveAppendEntriesRequest")
          ((msgLine e id s.vote m.src m.dst (elements cfg.incoming)).ev.name == "ReceiveSnapshot")) = false := by
        simp [msgLine, evConv, hname']
      have hn2 : ((msgLine e id s.vote m.src m.dst (elements cfg.incoming)).ev.name ==
          "ReceiveAppendEntriesResponse") = true := by simp [msgLine, evConv, hname']
      simp only [hn1, hn2, Bool.false_eq_true, ↓reduceIte]
      rw [← hmabs]
      rw [← msgLine_perm e id s.vote m.src m.dst xs _ hxs]
      exact isAEResp_appResp C C.length e id s.vote xs m tm hmsg hm hty hrej (by rw [hterm]; exact bt) bi
    · unfold Etcdraft.Trace.validatePreStates
      rw [hline, hmdst, hdst]
      have hsm := stateMatches_node C s (σ.s (idAbs id)) e id xs hR hs (by rw [hrole]; decide) hterm' hcommit' hrl
        hlog (hxs.trans hin) bt bc bl σ rfl hcontains
      rw [← msgLine_perm e id s.vote m.src id xs _ hxs, hts]
      have : (msgLine e id s.vote m.src id xs).stateMatches σ (idAbs id) = true := by
        unfold Etcdraft.Line.stateMatches at hsm ⊢
        simpa [msgLine, nodeLine] using hsm
      simp [this]

/-- **A one-round receive line's step** (generic): from a run reaching `σ`, a receive event whose
line `ln` parses, `mabs` the one message of the network the line matches (the pre-state validated),
received with the one successor `S` that consumes it, the invariants at `S`. -/
theorem simRun_recv1 (C : List w64) (L : List TraceEv) (σ S : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (ln : Etcdraft.Line) (mabs : Etcdraft.Msg)
    (hparse : Etcdraft.parseLine L.length (evConv e) = .ok ln)
    (hrecv : Etcdraft.isReceiveName ln.ev.name = true)
    (hnd : σ.messages.domain.Nodup) (hmem : mabs ∈ σ.messages.domain)
    (hmatch : recvPred ln mabs = true) (hpre : ln.stateMatches σ mabs.dest = true)
    (huniq : ∀ lines (ts : Etcdraft.TState), ts.s = σ → ∀ m' ∈ σ.messages.domain, m' ≠ mabs →
      (recvPred ln m' && (linesTrace C (lines ++ [ln])).validatePreStates ts m'.dest) = false)
    (hrcv : σ.receive mabs = .ok [S]) (hone : Etcdraft.oneLessMessage σ S mabs = true)
    (hboot : ∀ lines ln', parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln'])).getD L.length false = false)
    (hinv : S.violated = .ok none) :
    SimRun C (L ++ [e]) S := by
  apply simRun_snoc_chain C L σ _ e _ hrun hL hparse
  intro lines ts hl hts hl'
  have hlen := parseLines_length _ _ hl
  simp only [List.length_map] at hlen
  have hline := linesTrace_line_last C lines ln ts.l (by omega)
  subst hts
  have hrn : recvNext ts S mabs = { s := S, l := ts.l + 1, pl := ts.l } := by simp [recvNext, hone]
  refine ⟨{ s := S, l := ts.l + 1, pl := ts.l }, rfl, Chain.last _ ts _ ?_ rfl hinv⟩
  have := next_receive (linesTrace C (lines ++ [ln])) ts mabs S (by omega)
    (by simp [linesTrace, Etcdraft.Trace.len]; omega)
    (by simp only [linesTrace]; rw [hl']; simpa using hboot lines _ hl)
    (by rw [hline]; exact hrecv) hnd hmem (by rw [hline]; exact hmatch)
    (by unfold Etcdraft.Trace.validatePreStates; rw [hline, hpre]; simp)
    (fun m' hm' hne => by rw [hline]; exact huniq lines ts rfl m' hm' hne) hrcv
  rw [this, hrn]

/-- **A vote request's receive line's step** (of the node's term: `HandleRequestVoteRequest`, one
round). -/
theorem simRun_recvVoteReq (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (id : w64) (s : NState) (cfg : CfgM) (m : Msg)
    (hev : SendEvOf (W64 14) id s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : id ∈ C) (hsrv : σ.server = confAbs C)
    (hR : SimServerR C C.length (toPState s) (σ.s (idAbs id))) (hs : LogShapeOk C.length (toPState s))
    (hpre : s.role ≠ .preCandidate) (hty : m.ty = .vote) (hdst : m.dst = id) (hterm : m.term = s.term)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (bi : uint.Z m.index < 2 ^ 63)
    (blt : uint.Z m.logterm < 2 ^ 63)
    (hnd : σ.messages.domain.Nodup)
    (hmem : (msgAbs C C.length m).get (by simp [msgAbs, hty]) ∈ σ.messages.domain)
    (hcnt : 0 < Etcdraft.Bag.count σ.messages ((msgAbs C C.length m).get (by simp [msgAbs, hty])))
    (huniq : ∀ lines (ts : Etcdraft.TState), ts.s = σ → ∀ m' ∈ σ.messages.domain,
      m' ≠ (msgAbs C C.length m).get (by simp [msgAbs, hty]) →
      (recvPred (msgLine e id s.vote m.src m.dst (elements cfg.incoming)) m' &&
        (linesTrace C (lines ++ [msgLine e id s.vote m.src m.dst (elements cfg.incoming)])).validatePreStates ts
          m'.dest) = false)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinv : (voteReqResult σ (idAbs id) (idAbs m.src)
      ((msgAbs C C.length m).get (by simp [msgAbs, hty]))).violated = .ok none) :
    SimRun C (L ++ [e]) (voteReqResult σ (idAbs id) (idAbs m.src)
      ((msgAbs C C.length m).get (by simp [msgAbs, hty]))) := by
  obtain ⟨hname, hnid, hterm', hvote, hcommit', hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  have hname' : gsStr e.name = "ReceiveRequestVoteRequest" := by
    simp only [evtNames] at hname
    have : e.name = go!"ReceiveRequestVoteRequest" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  have htyp : tm.typ = msgTypeStr .vote := by rw [hm.1, hty]
  have hparse : Etcdraft.parseLine L.length (evConv e) = .ok (msgLine e id s.vote m.src m.dst (elements cfg.incoming)) := by
    rw [← msgLine_perm e id s.vote m.src m.dst xs _ hxs]
    exact parseLine_msg L.length e id s.vote m.src m.dst xs [] tm hnid hvote hconf hmsg hm.2.2.1 hm.2.2.2.1
      (by rw [htyp]; rfl) (by rw [hname']; decide)
  generalize hmabs : (msgAbs C C.length m).get (by simp [msgAbs, hty]) = mabs at *
  have hmt : mabs.type = .requestVoteRequest := by rw [← hmabs]; simp [msgAbs, hty]
  have hmterm : mabs.term = uint.Z m.term := by rw [← hmabs]; simp [msgAbs, hty]
  have hmsrc : mabs.source = idAbs m.src := by rw [← hmabs]; simp [msgAbs, hty]
  have hmdst : mabs.dest = idAbs m.dst := by rw [← hmabs]; simp [msgAbs, hty]
  have hcontains : σ.server.contains (idAbs id) = true := by
    rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  have hcur : mabs.term = (σ.s (idAbs id)).currentTerm := by rw [hR.1, hmterm, hterm]; rfl
  apply simRun_recv1 C L σ _ hrun hL e _ mabs hparse (by simp [msgLine, evConv, hname']; rfl) hnd hmem
  · unfold recvPred
    have hn1 : (or ((msgLine e id s.vote m.src m.dst (elements cfg.incoming)).ev.name == "ReceiveAppendEntriesRequest")
        ((msgLine e id s.vote m.src m.dst (elements cfg.incoming)).ev.name == "ReceiveSnapshot")) = false := by
      simp [msgLine, evConv, hname']
    have hn2 : ((msgLine e id s.vote m.src m.dst (elements cfg.incoming)).ev.name ==
        "ReceiveAppendEntriesResponse") = false := by simp [msgLine, evConv, hname']
    have hn3 : ((msgLine e id s.vote m.src m.dst (elements cfg.incoming)).ev.name ==
        "ReceiveRequestVoteRequest") = true := by simp [msgLine, evConv, hname']
    simp only [hn1, hn2, hn3, Bool.false_eq_true, ↓reduceIte]
    rw [← hmabs, ← msgLine_perm e id s.vote m.src m.dst xs _ hxs]
    exact isRVReq_vote C C.length e id s.vote xs m tm hmsg hm hty (by rw [hterm]; exact bt) bi blt
  · rw [hmdst, hdst, ← msgLine_perm e id s.vote m.src id xs _ hxs]
    have hsm := stateMatches_node C s (σ.s (idAbs id)) e id xs hR hs hpre hterm' hcommit' hrl
      hlog (hxs.trans hin) bt bc bl σ rfl hcontains
    unfold Etcdraft.Line.stateMatches at hsm ⊢
    simpa [msgLine, nodeLine] using hsm
  · exact huniq
  · have := receive_voteReq σ mabs (by rw [hmdst, hdst]; exact hcontains) hmt (by rw [hmdst, hdst]; exact hcur)
    rw [this, hmdst, hmsrc, hdst]
  · rw [← hdst, ← hmdst, ← hmsrc]
    exact oneLess_voteReq σ _ _ mabs (by rw [hmdst, hdst, hcur]; exact Int.le_refl _) hnd hcnt
  · exact hboot
  · exact hinv

/-- **A vote response's receive line's step** (at a candidate, of its term: `HandleRequestVoteResponse`,
one round). -/
theorem simRun_recvVoteResp (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (id : w64) (s : NState) (cfg : CfgM) (m : Msg)
    (hev : SendEvOf (W64 16) id s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : id ∈ C) (hsrv : σ.server = confAbs C)
    (hR : SimServerR C C.length (toPState s) (σ.s (idAbs id))) (hs : LogShapeOk C.length (toPState s))
    (hrole : s.role = .candidate) (hty : m.ty = .voteResp) (hdst : m.dst = id) (hterm : m.term = s.term)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63)
    (hnd : σ.messages.domain.Nodup)
    (hmem : (msgAbs C C.length m).get (by simp [msgAbs, hty]) ∈ σ.messages.domain)
    (hcnt : 0 < Etcdraft.Bag.count σ.messages ((msgAbs C C.length m).get (by simp [msgAbs, hty])))
    (huniq : ∀ lines (ts : Etcdraft.TState), ts.s = σ → ∀ m' ∈ σ.messages.domain,
      m' ≠ (msgAbs C C.length m).get (by simp [msgAbs, hty]) →
      (recvPred (msgLine e id s.vote m.src m.dst (elements cfg.incoming)) m' &&
        (linesTrace C (lines ++ [msgLine e id s.vote m.src m.dst (elements cfg.incoming)])).validatePreStates ts
          m'.dest) = false)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinv : (voteRespResult σ (idAbs id) (idAbs m.src)
      ((msgAbs C C.length m).get (by simp [msgAbs, hty]))).violated = .ok none) :
    SimRun C (L ++ [e]) (voteRespResult σ (idAbs id) (idAbs m.src)
      ((msgAbs C C.length m).get (by simp [msgAbs, hty]))) := by
  obtain ⟨hname, hnid, hterm', hvote, hcommit', hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  have hname' : gsStr e.name = "ReceiveRequestVoteResponse" := by
    simp only [evtNames] at hname
    have : e.name = go!"ReceiveRequestVoteResponse" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  have htyp : tm.typ = msgTypeStr .voteResp := by rw [hm.1, hty]
  have hparse : Etcdraft.parseLine L.length (evConv e) = .ok (msgLine e id s.vote m.src m.dst (elements cfg.incoming)) := by
    rw [← msgLine_perm e id s.vote m.src m.dst xs _ hxs]
    exact parseLine_msg L.length e id s.vote m.src m.dst xs [] tm hnid hvote hconf hmsg hm.2.2.1 hm.2.2.2.1
      (by rw [htyp]; rfl) (by rw [hname']; decide)
  generalize hmabs : (msgAbs C C.length m).get (by simp [msgAbs, hty]) = mabs at *
  have hmt : mabs.type = .requestVoteResponse := by rw [← hmabs]; simp [msgAbs, hty]
  have hmterm : mabs.term = uint.Z m.term := by rw [← hmabs]; simp [msgAbs, hty]
  have hmsrc : mabs.source = idAbs m.src := by rw [← hmabs]; simp [msgAbs, hty]
  have hmdst : mabs.dest = idAbs m.dst := by rw [← hmabs]; simp [msgAbs, hty]
  have hcontains : σ.server.contains (idAbs id) = true := by
    rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  have hcur : mabs.term = (σ.s (idAbs id)).currentTerm := by rw [hR.1, hmterm, hterm]; rfl
  apply simRun_recv1 C L σ _ hrun hL e _ mabs hparse (by simp [msgLine, evConv, hname']; rfl) hnd hmem
  · unfold recvPred
    have hn1 : (or ((msgLine e id s.vote m.src m.dst (elements cfg.incoming)).ev.name == "ReceiveAppendEntriesRequest")
        ((msgLine e id s.vote m.src m.dst (elements cfg.incoming)).ev.name == "ReceiveSnapshot")) = false := by
      simp [msgLine, evConv, hname']
    have hn2 : ((msgLine e id s.vote m.src m.dst (elements cfg.incoming)).ev.name ==
        "ReceiveAppendEntriesResponse") = false := by simp [msgLine, evConv, hname']
    have hn3 : ((msgLine e id s.vote m.src m.dst (elements cfg.incoming)).ev.name ==
        "ReceiveRequestVoteRequest") = false := by simp [msgLine, evConv, hname']
    simp only [hn1, hn2, hn3, Bool.false_eq_true, ↓reduceIte]
    rw [← hmabs, ← msgLine_perm e id s.vote m.src m.dst xs _ hxs]
    exact isRVResp_voteResp C C.length e id s.vote xs m tm hmsg hm hty (by rw [hterm]; exact bt)
  · rw [hmdst, hdst, ← msgLine_perm e id s.vote m.src id xs _ hxs]
    have hsm := stateMatches_node C s (σ.s (idAbs id)) e id xs hR hs (by rw [hrole]; decide) hterm' hcommit' hrl
      hlog (hxs.trans hin) bt bc bl σ rfl hcontains
    unfold Etcdraft.Line.stateMatches at hsm ⊢
    simpa [msgLine, nodeLine] using hsm
  · exact huniq
  · have hc : (σ.s mabs.dest).state = Etcdraft.candidate := by
      rw [hmdst, hdst, hR.2.1]; simp [toPState, hrole, proleRole]; rfl
    have := receive_voteResp σ mabs (by rw [hmdst, hdst]; exact hcontains) hmt (by rw [hmdst, hdst]; exact hcur) hc
    rw [this, hmdst, hmsrc, hdst]
  · exact oneLess_voteResp σ _ _ mabs hnd hcnt
  · exact hboot
  · exact hinv

/-- After a receive line's first round the pre-state is not checked again (`pl = l`). -/
theorem validatePre_later (t : Etcdraft.Trace) (l0 : Nat) (hl0 : l0 ≠ 0) (st : Etcdraft.State)
    (i : Etcdraft.ID) : t.validatePreStates ⟨st, l0, l0⟩ i = true := by
  unfold Etcdraft.Trace.validatePreStates; simp; omega

/-- **A truncation round's successor** at a later round of the line (the message the line matches
the one in the network; the state `st`'s server a follower whose log is the abstract `n` first
entries of `es`, conflicting with the batch). -/
theorem next_trunc (t : Etcdraft.Trace) (l0 pl : Nat) (st : Etcdraft.State) (mabs : Etcdraft.Msg)
    (C : List w64) (bl p n : Nat) (es ents : List EntryM)
    (hl0 : l0 ≠ 0) (hl : l0 ≤ t.len) (hb : t.bootstrap.getD (l0 - 1) false = false)
    (hrecv : Etcdraft.isReceiveName (t.line l0).ev.name = true)
    (hnd : st.messages.domain.Nodup) (hm : mabs ∈ st.messages.domain)
    (hmatch : recvPred (t.line l0) mabs = true)
    (hpre : t.validatePreStates ⟨st, l0, pl⟩ mabs.dest = true)
    (huniq : ∀ m' ∈ st.messages.domain, m' ≠ mabs → recvPred (t.line l0) m' = false)
    (hsrv : st.server.contains mabs.dest = true) (hty : mabs.type = .appendEntriesRequest)
    (hf : (st.s mabs.dest).state = Etcdraft.follower) (hterm : mabs.term = (st.s mabs.dest).currentTerm)
    (hsub : mabs.subtype ≠ "snapshot")
    (hlog : (st.s mabs.dest).log = logAbs C bl 1 (es.take n))
    (hents : mabs.entries = logAbs C bl (p + 1) ents) (hprev : mabs.prevLogIndex = p) (hn : n ≤ es.length)
    (hpn : p ≤ n) (hc : (st.s mabs.dest).commitIndex < (p : Int) + 1) (hne : ents ≠ [])
    (hbl : BootTerms bl 1 es) (hbe : BootTerms bl (p + 1) ents)
    (hlogOk : (or (mabs.prevLogIndex == 0) (decide (mabs.prevLogIndex > 0) && decide (mabs.prevLogIndex ≤ (st.s mabs.dest).log.length) &&
      some mabs.prevLogTerm == (((st.s mabs.dest).log[(mabs.prevLogIndex - 1).toNat]?).map Etcdraft.Entry.term))) = true)
    (hconf : ¬ ∀ k e, ents[k]? = some e → p + k < n → ((es.take n)[p + k]?).map EntryM.Term' = some e.Term') :
    t.next ⟨st, l0, pl⟩ = .ok [⟨truncSt st mabs.dest mabs.source (logAbs C bl 1 (es.take (n - 1))), l0, l0⟩] := by
  have hrcv := receive_trunc st mabs C bl p n es ents hsrv hty hf hterm hsub hlog hents hprev hn hpn hc hne hbl hbe
    hlogOk hconf
  have hone : Etcdraft.oneLessMessage st (truncSt st mabs.dest mabs.source (logAbs C bl 1 (es.take (n - 1))))
      mabs = false := by
    unfold Etcdraft.oneLessMessage
    have : (truncSt st mabs.dest mabs.source (logAbs C bl 1 (es.take (n - 1)))).messages = st.messages := rfl
    rw [this]; simp; intro h; rw [h]; decide
  have := next_receive t ⟨st, l0, pl⟩ mabs _ hl0 hl hb hrecv hnd hm hmatch hpre
    (fun m' hm' hne => by simp [huniq m' hm' hne]) hrcv
  rw [this]; simp [recvNext, hone]

/-- **The append round's successor** at a later round of the line. -/
theorem next_append (t : Etcdraft.Trace) (l0 pl : Nat) (st : Etcdraft.State) (mabs : Etcdraft.Msg)
    (C : List w64) (bl p : Nat) (L ents : List EntryM)
    (hl0 : l0 ≠ 0) (hl : l0 ≤ t.len) (hb : t.bootstrap.getD (l0 - 1) false = false)
    (hrecv : Etcdraft.isReceiveName (t.line l0).ev.name = true)
    (hnd : st.messages.domain.Nodup) (hm : mabs ∈ st.messages.domain)
    (hmatch : recvPred (t.line l0) mabs = true)
    (hpre : t.validatePreStates ⟨st, l0, pl⟩ mabs.dest = true)
    (huniq : ∀ m' ∈ st.messages.domain, m' ≠ mabs → recvPred (t.line l0) m' = false)
    (hsrv : st.server.contains mabs.dest = true) (hty : mabs.type = .appendEntriesRequest)
    (hf : (st.s mabs.dest).state = Etcdraft.follower) (hterm : mabs.term = (st.s mabs.dest).currentTerm)
    (hsub : mabs.subtype ≠ "snapshot")
    (hlog : (st.s mabs.dest).log = logAbs C bl 1 L)
    (hents : mabs.entries = logAbs C bl (p + 1) ents) (hprev : mabs.prevLogIndex = p) (hpq : p ≤ L.length)
    (hq : L.length < p + ents.length) (hc : (st.s mabs.dest).commitIndex < (p : Int) + 1)
    (hbl : BootTerms bl 1 L) (hbe : BootTerms bl (p + 1) ents)
    (hlogOk : (or (mabs.prevLogIndex == 0) (decide (mabs.prevLogIndex > 0) && decide (mabs.prevLogIndex ≤ (st.s mabs.dest).log.length) &&
      some mabs.prevLogTerm == (((st.s mabs.dest).log[(mabs.prevLogIndex - 1).toNat]?).map Etcdraft.Entry.term))) = true)
    (hnc : ∀ k e, ents[k]? = some e → p + k < L.length → (L[p + k]?).map EntryM.Term' = some e.Term') :
    t.next ⟨st, l0, pl⟩ = .ok [⟨truncSt st mabs.dest mabs.source
      (logAbs C bl 1 L ++ (logAbs C bl (p + 1) ents).drop (L.length - p)), l0, l0⟩] := by
  have hrcv := receive_append st mabs C bl p L ents hsrv hty hf hterm hsub hlog hents hprev hpq hq hc hbl hbe
    hlogOk hnc
  have hone : Etcdraft.oneLessMessage st (truncSt st mabs.dest mabs.source
      (logAbs C bl 1 L ++ (logAbs C bl (p + 1) ents).drop (L.length - p))) mabs = false := by
    unfold Etcdraft.oneLessMessage
    have : (truncSt st mabs.dest mabs.source
      (logAbs C bl 1 L ++ (logAbs C bl (p + 1) ents).drop (L.length - p))).messages = st.messages := rfl
    rw [this]; simp; intro h; rw [h]; decide
  have := next_receive t ⟨st, l0, pl⟩ mabs _ hl0 hl hb hrecv hnd hm hmatch hpre
    (fun m' hm' hne => by simp [huniq m' hm' hne]) hrcv
  rw [this]; simp [recvNext, hone]

/-- The state after `AppendEntriesAlreadyDone` of an accepted append request. -/
def doneSt (st : Etcdraft.State) (mabs : Etcdraft.Msg) (p k : Nat) : Etcdraft.State :=
  withLead ((st.commitTo mabs.dest (min mabs.commitIndex ((p : Int) + k))).reply { type := .appendEntriesResponse, subtype := mabs.subtype, term := (st.s mabs.dest).currentTerm, success := true, matchIndex := (p : Int) + k, source := mabs.dest, dest := mabs.source } mabs) mabs.dest mabs.source

/-- **The last round's successor**: the request consumed, on the next line. -/
theorem next_done (t : Etcdraft.Trace) (l0 pl : Nat) (st : Etcdraft.State) (mabs : Etcdraft.Msg)
    (C : List w64) (bl p : Nat) (L ents : List EntryM)
    (hl0 : l0 ≠ 0) (hl : l0 ≤ t.len) (hb : t.bootstrap.getD (l0 - 1) false = false)
    (hrecv : Etcdraft.isReceiveName (t.line l0).ev.name = true)
    (hnd : st.messages.domain.Nodup) (hm : mabs ∈ st.messages.domain)
    (hcnt : 0 < Etcdraft.Bag.count st.messages mabs)
    (hmatch : recvPred (t.line l0) mabs = true)
    (hpre : t.validatePreStates ⟨st, l0, pl⟩ mabs.dest = true)
    (huniq : ∀ m' ∈ st.messages.domain, m' ≠ mabs → recvPred (t.line l0) m' = false)
    (hsrv : st.server.contains mabs.dest = true) (hty : mabs.type = .appendEntriesRequest)
    (hf : (st.s mabs.dest).state = Etcdraft.follower) (hterm : mabs.term = (st.s mabs.dest).currentTerm)
    (hsub : mabs.subtype = "app")
    (hlog : (st.s mabs.dest).log = logAbs C bl 1 L)
    (hents : mabs.entries = logAbs C bl (p + 1) ents) (hprev : mabs.prevLogIndex = p)
    (hq : p + ents.length ≤ L.length) (hc : (st.s mabs.dest).commitIndex < (p : Int) + 1)
    (hbl : BootTerms bl 1 L) (hbe : BootTerms bl (p + 1) ents)
    (hlogOk : (or (mabs.prevLogIndex == 0) (decide (mabs.prevLogIndex > 0) && decide (mabs.prevLogIndex ≤ (st.s mabs.dest).log.length) &&
      some mabs.prevLogTerm == (((st.s mabs.dest).log[(mabs.prevLogIndex - 1).toNat]?).map Etcdraft.Entry.term))) = true)
    (hnc : ∀ k e, ents[k]? = some e → p + k < L.length → (L[p + k]?).map EntryM.Term' = some e.Term') :
    t.next ⟨st, l0, pl⟩ = .ok [⟨doneSt st mabs p ents.length, l0 + 1, l0⟩] := by
  have hrcv : st.receive mabs = .ok [doneSt st mabs p ents.length] :=
    receive_done st mabs C bl p L ents hsrv hty hf hterm hsub hlog hents hprev hq hc hbl hbe hlogOk hnc
  have hone : Etcdraft.oneLessMessage st (doneSt st mabs p ents.length) mabs = true := by
    have hmsgs : (doneSt st mabs p ents.length).messages = (st.discard mabs).messages := rfl
    have h := oneLess_discard st st mabs rfl hnd hcnt
    unfold Etcdraft.oneLessMessage at h ⊢
    rw [hmsgs]; exact h
  have := next_receive t ⟨st, l0, pl⟩ mabs _ hl0 hl hb hrecv hnd hm hmatch hpre
    (fun m' hm' hne => by simp [huniq m' hm' hne]) hrcv
  rw [this]; simp only [recvNext, hone, ↓reduceIte]

theorem truncSt_facts (st : Etcdraft.State) (i j : Etcdraft.ID) (L : List Etcdraft.Entry) :
    (truncSt st i j L).server = st.server ∧ (truncSt st i j L).messages = st.messages ∧
    ((truncSt st i j L).s i).state = (st.s i).state ∧
    ((truncSt st i j L).s i).currentTerm = (st.s i).currentTerm ∧
    ((truncSt st i j L).s i).commitIndex = (st.s i).commitIndex ∧ ((truncSt st i j L).s i).log = L := by
  simp [truncSt, withLead, Etcdraft.State.upd]

/-- **An accepted append request's line, with a conflict** (raft's `maybeAppend` truncating at the
batch's `d`-th entry, `p + d` past the log's start): the specification's rounds from the line's
first state, the truncations down to `p + d`, the append, `AppendEntriesAlreadyDone`, as a chain. -/
theorem chain_appConflict (t : Etcdraft.Trace) (l0 pl0 : Nat) (σ : Etcdraft.State) (mabs : Etcdraft.Msg)
    (C : List w64) (bl p d : Nat) (es ents : List EntryM) (pre : List Etcdraft.TState)
    (hpreT : ∀ v ∈ pre, mabs.dest ∈ v.s.server ∧ (v.s.s mabs.dest).currentTerm ≠ (σ.s mabs.dest).currentTerm)
    (hl0 : l0 ≠ 0) (hl : l0 ≤ t.len) (hb : t.bootstrap.getD (l0 - 1) false = false)
    (hrecv : Etcdraft.isReceiveName (t.line l0).ev.name = true)
    (hnd : σ.messages.domain.Nodup) (hm : mabs ∈ σ.messages.domain)
    (hcnt : 0 < Etcdraft.Bag.count σ.messages mabs)
    (hmatch : recvPred (t.line l0) mabs = true)
    (hpre0 : t.validatePreStates ⟨σ, l0, pl0⟩ mabs.dest = true)
    (huniq : ∀ m' ∈ σ.messages.domain, m' ≠ mabs → recvPred (t.line l0) m' = false)
    (hsrv : σ.server.contains mabs.dest = true) (hty : mabs.type = .appendEntriesRequest)
    (hf : (σ.s mabs.dest).state = Etcdraft.follower) (hterm : mabs.term = (σ.s mabs.dest).currentTerm)
    (hsub : mabs.subtype = "app")
    (hlog : (σ.s mabs.dest).log = logAbs C bl 1 es)
    (hents : mabs.entries = logAbs C bl (p + 1) ents) (hprev : mabs.prevLogIndex = p)
    (hc : (σ.s mabs.dest).commitIndex < (p : Int) + 1)
    (hbl : BootTerms bl 1 es) (hbe : BootTerms bl (p + 1) ents)
    (hd : d < ents.length) (hpd : p + d ≤ es.length)
    (hbef : ∀ k e, ents[k]? = some e → p + k < p + d →
      ((es.take (p + d))[p + k]?).map EntryM.Term' = some e.Term')
    (hconf : ∀ n, p + d < n → n ≤ es.length → ¬ ∀ k e, ents[k]? = some e → p + k < n →
      ((es.take n)[p + k]?).map EntryM.Term' = some e.Term')
    (hmis : p + d < es.length → ∃ e, ents[d]? = some e ∧ (es[p + d]?).map EntryM.Term' ≠ some e.Term')
    (hok : ∀ k, p + d ≤ k → k ≤ es.length → LogOkL mabs (logAbs C bl 1 (es.take k)) = true)
    (hokA : LogOkL mabs (logAbs C bl 1 (es.take (p + d) ++ ents.drop d)) = true)
    (hinvT : ∀ k, p + d ≤ k → k < es.length →
      (truncSt σ mabs.dest mabs.source (logAbs C bl 1 (es.take k))).violated = .ok none)
    (hinvA : (truncSt σ mabs.dest mabs.source (logAbs C bl 1 (es.take (p + d) ++ ents.drop d))).violated = .ok none)
    (hinvD : (doneSt (truncSt σ mabs.dest mabs.source (logAbs C bl 1 (es.take (p + d) ++ ents.drop d)))
      mabs p ents.length).violated = .ok none) :
    Chain t l0 (pre ++ [⟨σ, l0, pl0⟩]) ⟨σ, l0, pl0⟩
      ⟨doneSt (truncSt σ mabs.dest mabs.source (logAbs C bl 1 (es.take (p + d) ++ ents.drop d)))
        mabs p ents.length, l0 + 1, l0⟩ := by
  -- the log after the batch, and its facts
  have hne : ents ≠ [] := by intro h; rw [h] at hd; simp at hd
  have hdrop : (es.take (p + d)).length - p = d := by simp; omega
  have hlenT : (es.take (p + d)).length = p + d := by simp; omega
  have hlenA : (es.take (p + d) ++ ents.drop d).length = p + ents.length := by simp; omega
  have hncA := truncAppend_has es ents p d hpd hbef
  have hblA := bootTerms_truncAppend bl p d es ents hpd hbl hbe
  have hlogA : logAbs C bl 1 (es.take (p + d)) ++ (logAbs C bl (p + 1) ents).drop ((es.take (p + d)).length - p) =
      logAbs C bl 1 (es.take (p + d) ++ ents.drop d) := by
    rw [hdrop]; exact logAbs_truncAppend C bl p d es ents hpd
  obtain ⟨A, hA⟩ : ∃ A, truncSt σ mabs.dest mabs.source (logAbs C bl 1 (es.take (p + d) ++ ents.drop d)) = A :=
    ⟨_, rfl⟩
  rw [hA] at hinvA hinvD ⊢
  have hAf := truncSt_facts σ mabs.dest mabs.source (logAbs C bl 1 (es.take (p + d) ++ ents.drop d))
  rw [hA] at hAf
  obtain ⟨hAsrv, hAmsg, hAst, hAterm, hAcom, hAlog⟩ := hAf
  -- the last round, from the batch appended
  have hlast : ∀ visited, Chain t l0 visited ⟨A, l0, l0⟩ ⟨doneSt A mabs p ents.length, l0 + 1, l0⟩ := by
    intro visited
    refine Chain.last visited ⟨A, l0, l0⟩ ⟨doneSt A mabs p ents.length, l0 + 1, l0⟩ ?_ rfl hinvD
    apply next_done t l0 l0 A mabs C bl p (es.take (p + d) ++ ents.drop d) ents hl0 hl hb hrecv
      (by rw [hAmsg]; exact hnd) (by rw [hAmsg]; exact hm) (by rw [hAmsg]; exact hcnt) hmatch
      (validatePre_later t l0 hl0 A _) (by rw [hAmsg]; exact huniq) (by rw [hAsrv]; exact hsrv) hty
      (by rw [hAst]; exact hf) (by rw [hAterm]; exact hterm) hsub hAlog hents hprev (by omega)
      (by rw [hAcom]; exact hc) hblA hbe
      (by have := hokA; unfold LogOkL at this; rw [hAlog]; exact this) hncA
  -- the append round, from a state whose server's log is the abstract `p + d` first entries
  have happ : ∀ (X : Etcdraft.State) (pl : Nat), t.validatePreStates ⟨X, l0, pl⟩ mabs.dest = true →
      X.messages = σ.messages → X.server = σ.server → (X.s mabs.dest).state = (σ.s mabs.dest).state →
      (X.s mabs.dest).currentTerm = (σ.s mabs.dest).currentTerm →
      (X.s mabs.dest).commitIndex = (σ.s mabs.dest).commitIndex →
      (X.s mabs.dest).log = logAbs C bl 1 (es.take (p + d)) →
      truncSt X mabs.dest mabs.source (logAbs C bl 1 (es.take (p + d) ++ ents.drop d)) = A →
      t.next ⟨X, l0, pl⟩ = .ok [⟨A, l0, l0⟩] := by
    intro X pl hpre hXm hXs hXst hXt hXc hXl hXA
    rw [← hXA, ← hlogA]
    apply next_append t l0 pl X mabs C bl p (es.take (p + d)) ents hl0 hl hb hrecv (by rw [hXm]; exact hnd)
      (by rw [hXm]; exact hm) hmatch hpre (by rw [hXm]; exact huniq) (by rw [hXs]; exact hsrv) hty
      (by rw [hXst]; exact hf) (by rw [hXt]; exact hterm) (by rw [hsub]; decide) hXl hents hprev (by omega)
      (by omega) (by rw [hXc]; exact hc) (hbl.take _) hbe
      (by have := hok (p + d) (Nat.le_refl _) hpd; unfold LogOkL at this; rw [hXl]; exact this)
      (by rw [hlenT]; exact hbef)
  have hdestσ : mabs.dest ∈ σ.server := List.contains_iff_mem.1 hsrv
  have hlenAne : ∀ k, k ≤ p + d → logAbs C bl 1 (es.take k) ≠ logAbs C bl 1 (es.take (p + d) ++ ents.drop d) := by
    intro k hk h
    have := congrArg List.length h
    rw [logAbs_length, logAbs_length, hlenA] at this
    simp at this; omega
  rcases Nat.lt_or_ge (p + d) es.length with hlt | hge
  · -- truncations first: `S k` the state with the abstract `k` first entries
    obtain ⟨e, he, hmise⟩ := hmis hlt
    have hAne : ∀ k, p + d < k → k ≤ es.length →
        logAbs C bl 1 (es.take k) ≠ logAbs C bl 1 (es.take (p + d) ++ ents.drop d) := by
      intro k hk1 hk2 h
      have h2 := congrArg (fun L => (L[p + d]?).map Etcdraft.Entry.term) h
      simp only [logAbs_getElem?] at h2
      rw [List.getElem?_take_of_lt hk1, List.getElem?_append_right (by simp; omega), List.getElem?_drop] at h2
      simp only [hlenT, Nat.sub_self, Nat.add_zero, he] at h2
      obtain ⟨x, hx⟩ : ∃ x, es[p + d]? = some x := ⟨es[p + d], List.getElem?_eq_getElem hlt⟩
      rw [hx] at h2 hmise
      simp only [Option.map_some, Option.some.injEq] at h2 hmise
      rw [entAbs_term C bl _ x (fun hb => hbl (p + d) x (by omega) hx),
        entAbs_term C bl _ e (fun hb => hbe d e (by omega) he)] at h2
      exact hmise (congrArg some (uint_Z_inj.mp h2))
    let S : Nat → Etcdraft.State := fun k => truncSt σ mabs.dest mabs.source (logAbs C bl 1 (es.take k))
    have hSf : ∀ k, (S k).server = σ.server ∧ (S k).messages = σ.messages ∧
        ((S k).s mabs.dest).state = (σ.s mabs.dest).state ∧
        ((S k).s mabs.dest).currentTerm = (σ.s mabs.dest).currentTerm ∧
        ((S k).s mabs.dest).commitIndex = (σ.s mabs.dest).commitIndex ∧
        ((S k).s mabs.dest).log = logAbs C bl 1 (es.take k) := fun k => truncSt_facts _ _ _ _
    have htr : ∀ k, p + d < k → k ≤ es.length → ∀ (X : Etcdraft.State) (pl : Nat),
        t.validatePreStates ⟨X, l0, pl⟩ mabs.dest = true → X.messages = σ.messages → X.server = σ.server →
        (X.s mabs.dest).state = (σ.s mabs.dest).state →
        (X.s mabs.dest).currentTerm = (σ.s mabs.dest).currentTerm →
        (X.s mabs.dest).commitIndex = (σ.s mabs.dest).commitIndex →
        (X.s mabs.dest).log = logAbs C bl 1 (es.take k) →
        truncSt X mabs.dest mabs.source (logAbs C bl 1 (es.take (k - 1))) = S (k - 1) →
        t.next ⟨X, l0, pl⟩ = .ok [⟨S (k - 1), l0, l0⟩] := by
      intro k hk1 hk2 X pl hpre hXm hXs hXst hXt hXc hXl hXS
      rw [← hXS]
      exact next_trunc t l0 pl X mabs C bl p k es ents hl0 hl hb hrecv (by rw [hXm]; exact hnd)
        (by rw [hXm]; exact hm) hmatch hpre (by rw [hXm]; exact huniq) (by rw [hXs]; exact hsrv) hty
        (by rw [hXst]; exact hf) (by rw [hXt]; exact hterm) (by rw [hsub]; decide) hXl hents hprev hk2 (by omega)
        (by rw [hXc]; exact hc) hne hbl hbe
        (by have := hok k (by omega) hk2; unfold LogOkL at this; rw [hXl]; exact this) (hconf k hk1 hk2)
    have hlogN : (σ.s mabs.dest).log = logAbs C bl 1 (es.take es.length) := by rw [List.take_length, hlog]
    apply Chain.step _ _ ⟨S (es.length - 1), l0, l0⟩ _
      (htr es.length hlt (Nat.le_refl _) σ pl0 hpre0 rfl rfl rfl rfl rfl hlogN rfl) rfl
      (memEq_false_of_logs_or_term _ _ mabs.dest (by
        intro v hv
        rw [List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | rfl
        · obtain ⟨hvs, hvt⟩ := hpreT v hv
          exact ⟨hvs, Or.inr (by simp only; rw [(hSf _).2.2.2.1]; exact hvt)⟩
        refine ⟨hdestσ, Or.inl ?_⟩
        simp only; rw [hlogN, (hSf _).2.2.2.2.2]; exact logAbs_take_ne C bl es _ _ (Nat.le_refl _) (by omega) (by omega)))
      (hinvT _ (by omega) (by omega))
    have hcd := chain_down t l0 mabs.dest S (fun k => logAbs C bl 1 (es.take k)) (p + d) es.length
      ⟨doneSt A mabs p ents.length, l0 + 1, l0⟩ (σ.s mabs.dest).currentTerm (fun k => (hSf k).2.2.2.1)
      (fun k hk1 hk2 => htr k hk1 hk2 (S k) l0 (validatePre_later t l0 hl0 _ _) (hSf k).2.1 (hSf k).1
        (hSf k).2.2.1 (hSf k).2.2.2.1 (hSf k).2.2.2.2.1 (hSf k).2.2.2.2.2 (truncSt_truncSt _ _ _ _ _))
      (fun k => by rw [(hSf k).1]; exact hdestσ) (fun k => (hSf k).2.2.2.2.2)
      (fun k k' hk hk' hne => logAbs_take_ne C bl es k k' hk hk' hne)
      (fun k hk1 hk2 => hinvT k hk1 hk2)
      (by
        intro visited hvis
        apply Chain.step visited ⟨S (p + d), l0, l0⟩ ⟨A, l0, l0⟩ _
          (happ (S (p + d)) l0 (validatePre_later t l0 hl0 _ _) (hSf _).2.1 (hSf _).1 (hSf _).2.2.1
            (hSf _).2.2.2.1 (hSf _).2.2.2.2.1 (hSf _).2.2.2.2.2 (by rw [truncSt_truncSt, hA])) rfl
          (memEq_false_of_logs_or_term _ _ mabs.dest (by
            intro v hv
            obtain ⟨hvs, hor⟩ := hvis v hv
            refine ⟨hvs, ?_⟩
            rcases hor with ⟨k', hk1, hk2, hk⟩ | ht
            · left; simp only; rw [hk, hAlog]
              rcases Nat.lt_or_ge (p + d) k' with h | h
              · exact hAne k' h hk2
              · exact hlenAne k' h
            · right; simp only; rw [hAterm]; exact ht))
          hinvA (hlast _))
      (es.length - 1 - (p + d))
      ((pre ++ [⟨σ, l0, pl0⟩]) ++ [⟨S (es.length - 1), l0, l0⟩]) (by omega)
      (by
        intro v hv
        rw [List.mem_append, List.mem_append, List.mem_singleton, List.mem_singleton] at hv
        rcases hv with (hv | rfl) | rfl
        · obtain ⟨hvs, hvt⟩ := hpreT v hv; exact ⟨hvs, Or.inr hvt⟩
        · exact ⟨hdestσ, Or.inl ⟨es.length, by omega, Nat.le_refl _, by simp only; rw [hlogN]⟩⟩
        · exact ⟨by rw [(hSf _).1]; exact hdestσ, Or.inl ⟨es.length - 1, by omega, by omega, (hSf _).2.2.2.2.2⟩⟩)
    have hk : p + d + (es.length - 1 - (p + d)) = es.length - 1 := by omega
    rw [hk] at hcd
    exact hcd
  · -- the conflicting entry just past the log's end: the append first
    have heq : p + d = es.length := by omega
    have hlogT : (σ.s mabs.dest).log = logAbs C bl 1 (es.take (p + d)) := by rw [hlog, heq, List.take_length]
    apply Chain.step _ _ ⟨A, l0, l0⟩ _ (happ σ pl0 hpre0 rfl rfl rfl rfl rfl hlogT hA) rfl
      (memEq_false_of_logs_or_term _ _ mabs.dest (by
        intro v hv
        rw [List.mem_append, List.mem_singleton] at hv
        rcases hv with hv | rfl
        · obtain ⟨hvs, hvt⟩ := hpreT v hv
          exact ⟨hvs, Or.inr (by simp only; rw [hAterm]; exact hvt)⟩
        refine ⟨hdestσ, Or.inl ?_⟩
        simp only; rw [hlogT, hAlog]; exact hlenAne _ (Nat.le_refl _)))
      hinvA (hlast _)

/-- **An accepted append request's line without a conflict** (every entry of the batch in the log):
one round, `AppendEntriesAlreadyDone`. -/
theorem chain_appNoConflict (t : Etcdraft.Trace) (l0 pl0 : Nat) (σ : Etcdraft.State) (mabs : Etcdraft.Msg)
    (C : List w64) (bl p : Nat) (es ents : List EntryM) (pre : List Etcdraft.TState)
    (hl0 : l0 ≠ 0) (hl : l0 ≤ t.len) (hb : t.bootstrap.getD (l0 - 1) false = false)
    (hrecv : Etcdraft.isReceiveName (t.line l0).ev.name = true)
    (hnd : σ.messages.domain.Nodup) (hm : mabs ∈ σ.messages.domain)
    (hcnt : 0 < Etcdraft.Bag.count σ.messages mabs)
    (hmatch : recvPred (t.line l0) mabs = true)
    (hpre0 : t.validatePreStates ⟨σ, l0, pl0⟩ mabs.dest = true)
    (huniq : ∀ m' ∈ σ.messages.domain, m' ≠ mabs → recvPred (t.line l0) m' = false)
    (hsrv : σ.server.contains mabs.dest = true) (hty : mabs.type = .appendEntriesRequest)
    (hf : (σ.s mabs.dest).state = Etcdraft.follower) (hterm : mabs.term = (σ.s mabs.dest).currentTerm)
    (hsub : mabs.subtype = "app")
    (hlog : (σ.s mabs.dest).log = logAbs C bl 1 es)
    (hents : mabs.entries = logAbs C bl (p + 1) ents) (hprev : mabs.prevLogIndex = p)
    (hq : p + ents.length ≤ es.length) (hc : (σ.s mabs.dest).commitIndex < (p : Int) + 1)
    (hbl : BootTerms bl 1 es) (hbe : BootTerms bl (p + 1) ents)
    (hok : LogOkL mabs (logAbs C bl 1 es) = true)
    (hnc : ∀ k e, ents[k]? = some e → p + k < es.length → (es[p + k]?).map EntryM.Term' = some e.Term')
    (hinvD : (doneSt σ mabs p ents.length).violated = .ok none) :
    Chain t l0 (pre ++ [⟨σ, l0, pl0⟩]) ⟨σ, l0, pl0⟩ ⟨doneSt σ mabs p ents.length, l0 + 1, l0⟩ :=
  Chain.last _ ⟨σ, l0, pl0⟩ ⟨doneSt σ mabs p ents.length, l0 + 1, l0⟩
    (next_done t l0 pl0 σ mabs C bl p es ents hl0 hl hb hrecv hnd hm hcnt hmatch hpre0 huniq hsrv hty hf hterm
      hsub hlog hents hprev hq hc hbl hbe (by have := hok; unfold LogOkL at this; rw [hlog]; exact this) hnc)
    rfl hinvD

/-- The last round's state does not depend on the leader having been adopted before (a log set to
itself). -/
theorem doneSt_truncSt_same (σ : Etcdraft.State) (mabs : Etcdraft.Msg) (p k : Nat)
    (L : List Etcdraft.Entry) (hL : (σ.s mabs.dest).log = L) :
    doneSt (truncSt σ mabs.dest mabs.source L) mabs p k = doneSt σ mabs p k := by
  unfold doneSt truncSt withLead
  simp only [Etcdraft.State.commitTo, Etcdraft.State.reply, Etcdraft.State.upd]
  congr 1
  funext x
  by_cases hx : x = mabs.dest
  · subst hx; simp [← hL]
  · simp [hx]

/-- **An accepted append request's line, from raft's `maybeAppend`** (the log `es`, uncompacted; the
batch `ents` after index `p`, of the previous term `lt`; the new log `es'`): the specification's
rounds as a chain, ending at `AppendEntriesAlreadyDone`'s state over the new log. -/
theorem chain_appAccept (t : Etcdraft.Trace) (l0 pl0 : Nat) (σ : Etcdraft.State) (mabs : Etcdraft.Msg)
    (C : List w64) (bl p : Nat) (lt lastnewi : w64) (es ents es' : List EntryM) (pre : List Etcdraft.TState)
    (hpreT : ∀ v ∈ pre, mabs.dest ∈ v.s.server ∧ (v.s.s mabs.dest).currentTerm ≠ (σ.s mabs.dest).currentTerm)
    (hl0 : l0 ≠ 0) (hl : l0 ≤ t.len) (hb : t.bootstrap.getD (l0 - 1) false = false)
    (hrecv : Etcdraft.isReceiveName (t.line l0).ev.name = true)
    (hnd : σ.messages.domain.Nodup) (hm : mabs ∈ σ.messages.domain)
    (hcnt : 0 < Etcdraft.Bag.count σ.messages mabs)
    (hmatch : recvPred (t.line l0) mabs = true)
    (hpre0 : t.validatePreStates ⟨σ, l0, pl0⟩ mabs.dest = true)
    (huniq : ∀ m' ∈ σ.messages.domain, m' ≠ mabs → recvPred (t.line l0) m' = false)
    (hsrv : σ.server.contains mabs.dest = true) (hty : mabs.type = .appendEntriesRequest)
    (hf : (σ.s mabs.dest).state = Etcdraft.follower) (hterm : mabs.term = (σ.s mabs.dest).currentTerm)
    (hsub : mabs.subtype = "app")
    (hlog : (σ.s mabs.dest).log = logAbs C bl 1 es)
    (hents : mabs.entries = logAbs C bl (p + 1) ents) (hprev : mabs.prevLogIndex = p)
    (hpt : mabs.prevLogTerm = uint.Z lt) (hlt0 : p = 0 → lt = W64 0)
    (hc : (σ.s mabs.dest).commitIndex < (p : Int) + 1)
    (hbl : BootTerms bl 1 es) (hbe : BootTerms bl (p + 1) ents)
    (hwf : ∀ (k : Nat) (e : EntryM), ents[k]? = some e → uint.Z e.Index' = (p : Int) + k + 1)
    (hp : p < 2 ^ 64) (hnw : (p : Int) + ents.length + 1 < 2 ^ 64)
    (happ : plogMaybeAppend (entryID.mk (W64 0) (W64 0)) es (entryID.mk lt (W64 p)) ents = some (lastnewi, es'))
    (hinvT : ∀ k, p ≤ k → k < es.length →
      (truncSt σ mabs.dest mabs.source (logAbs C bl 1 (es.take k))).violated = .ok none)
    (hinvA : (truncSt σ mabs.dest mabs.source (logAbs C bl 1 es')).violated = .ok none)
    (hinvD : (doneSt (truncSt σ mabs.dest mabs.source (logAbs C bl 1 es')) mabs p ents.length).violated = .ok none) :
    Chain t l0 (pre ++ [⟨σ, l0, pl0⟩]) ⟨σ, l0, pl0⟩
      ⟨doneSt (truncSt σ mabs.dest mabs.source (logAbs C bl 1 es')) mabs p ents.length, l0 + 1, l0⟩ := by
  have hpz : uint.Z (W64 p) = p := by word
  have hwf' : PlogWf (entryID.mk lt (W64 p)) ents := by
    intro k e he; have := hwf k e he; simp only [hpz]; push_cast; omega
  obtain ⟨hmatchP, -, -⟩ := plogMaybeAppend_inv _ _ _ _ _ _ hwf' (by simp only [hpz]; exact hnw) happ
  obtain ⟨hpl, -, hcase⟩ := maybeAppend_spec es ents es' p lt lastnewi hwf hp hnw happ
  have hokP : ∀ es2 : List EntryM, BootTerms bl 1 es2 → (∀ k, k < p → es2[k]? = es[k]?) →
      LogOkL mabs (logAbs C bl 1 es2) = true := by
    intro es2 hb2 hpre
    rw [logOkL_abs C bl mabs es2 p lt hprev hpt hb2 hlt0 hp, decide_eq_true_iff]
    exact (plogMatches_prefix es es2 lt p hp hpre).2 hmatchP
  rcases hcase with ⟨rfl, hq, hnc⟩ | ⟨d, hd, hpd, rfl, -, -, hbef, hconf⟩
  · rw [doneSt_truncSt_same σ mabs p ents.length _ hlog]
    exact chain_appNoConflict t l0 pl0 σ mabs C bl p es' ents pre hl0 hl hb hrecv hnd hm hcnt hmatch hpre0 huniq hsrv
      hty hf hterm hsub hlog hents hprev hq hc hbl hbe (hokP es' hbl (fun _ _ => rfl)) hnc
      (by rw [← doneSt_truncSt_same σ mabs p ents.length _ hlog]; exact hinvD)
  · have hmis : p + d < es.length → ∃ e, ents[d]? = some e ∧ (es[p + d]?).map EntryM.Term' ≠ some e.Term' := by
      intro hlt
      obtain ⟨e, he⟩ : ∃ e, ents[d]? = some e := ⟨ents[d], List.getElem?_eq_getElem hd⟩
      refine ⟨e, he, fun hmt => hconf (p + d + 1) (by omega) (by omega) ?_⟩
      intro k e' hk hlk
      rw [List.getElem?_take_of_lt hlk]
      rcases Nat.lt_or_ge k d with hkd | hkd
      · have := hbef k e' hk (by omega)
        rwa [List.getElem?_take_of_lt (by omega)] at this
      · have : k = d := by omega
        subst this; rw [he] at hk; cases hk; exact hmt
    exact chain_appConflict t l0 pl0 σ mabs C bl p d es ents pre hpreT hl0 hl hb hrecv hnd hm hcnt hmatch hpre0 huniq hsrv
      hty hf hterm hsub hlog hents hprev hc hbl hbe hd hpd hbef hconf hmis
      (fun k hk1 hk2 => hokP _ (hbl.take k) (fun k' hk' => List.getElem?_take_of_lt (by omega)))
      (hokP _ (bootTerms_truncAppend bl p d es ents hpd hbl hbe) (fun k' hk' => by
        rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt (by omega)]))
      (fun k hk1 hk2 => hinvT k (by omega) hk2) hinvA hinvD

/-- **An accepted append request's receive line's step** (at a follower of its term, raft's
`maybeAppend` succeeding: the rule `appAccept`): the specification's truncations, append and
`AppendEntriesAlreadyDone`, over the new log. -/
theorem simRun_recvApp (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (id : w64) (s : NState) (cfg : CfgM) (m : Msg)
    (hev : SendEvOf (W64 10) id s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : id ∈ C) (hsrv : σ.server = confAbs C)
    (hR : SimServerR C C.length (toPState s) (σ.s (idAbs id))) (hs : LogShapeOk C.length (toPState s))
    (hrole : s.role = .follower) (hty : m.ty = .app) (hdst : m.dst = id) (hterm : m.term = s.term)
    (hcom : uint.Z (toPState s).commit ≤ uint.Z m.index)
    (lastnewi : w64) (es' : List EntryM)
    (happ : plogMaybeAppend (entryID.mk (W64 0) (W64 0)) (toPState s).log
      (entryID.mk m.logterm (W64 (uint.nat m.index))) m.entries = some (lastnewi, es'))
    (hbe : BootTerms C.length (uint.nat m.index + 1) m.entries)
    (hwf : ∀ (k : Nat) (x : EntryM), m.entries[k]? = some x → uint.Z x.Index' = (uint.nat m.index : Int) + k + 1)
    (hlt0 : uint.nat m.index = 0 → m.logterm = W64 0)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (bi : uint.Z m.index < 2 ^ 63)
    (blt : uint.Z m.logterm < 2 ^ 63) (bk : m.entries.length < 2 ^ 63) (bmc : uint.Z m.commit < 2 ^ 63)
    (hnw : (uint.nat m.index : Int) + m.entries.length + 1 < 2 ^ 64)
    (hnd : σ.messages.domain.Nodup)
    (hmem : (msgAbs C C.length m).get (by simp [msgAbs, hty]) ∈ σ.messages.domain)
    (hcnt : 0 < Etcdraft.Bag.count σ.messages ((msgAbs C C.length m).get (by simp [msgAbs, hty])))
    (huniq : ∀ m' ∈ σ.messages.domain, m' ≠ (msgAbs C C.length m).get (by simp [msgAbs, hty]) →
      recvPred (msgLine e id s.vote m.src m.dst (elements cfg.incoming)) m' = false)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinvT : ∀ k, uint.nat m.index ≤ k → k < (toPState s).log.length →
      (truncSt σ (idAbs id) (idAbs m.src) (logAbs C C.length 1 ((toPState s).log.take k))).violated = .ok none)
    (hinvA : (truncSt σ (idAbs id) (idAbs m.src) (logAbs C C.length 1 es')).violated = .ok none)
    (hinvD : (doneSt (truncSt σ (idAbs id) (idAbs m.src) (logAbs C C.length 1 es'))
      ((msgAbs C C.length m).get (by simp [msgAbs, hty])) (uint.nat m.index) m.entries.length).violated = .ok none) :
    SimRun C (L ++ [e]) (doneSt (truncSt σ (idAbs id) (idAbs m.src) (logAbs C C.length 1 es'))
      ((msgAbs C C.length m).get (by simp [msgAbs, hty])) (uint.nat m.index) m.entries.length) := by
  subst hdst
  obtain ⟨hname, hnid, hterm', hvote, hcommit', hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  have hname' : gsStr e.name = "ReceiveAppendEntriesRequest" := by
    simp only [evtNames] at hname
    have : e.name = go!"ReceiveAppendEntriesRequest" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  have htyp : tm.typ = msgTypeStr .app := by rw [hm.1, hty]
  have hparse : Etcdraft.parseLine L.length (evConv e) = .ok (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) := by
    rw [← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    exact parseLine_msg L.length e m.dst s.vote m.src m.dst xs [] tm hnid hvote hconf hmsg hm.2.2.1 hm.2.2.2.1
      (by rw [htyp]; rfl) (by rw [hname']; decide)
  have hidxZ : ((uint.nat m.index : Nat) : Int) = uint.Z m.index := by word
  have hpred : recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming))
      ((msgAbs C C.length m).get (by simp [msgAbs, hty])) = true := by
    unfold recvPred
    have hn1 : (or ((msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)).ev.name == "ReceiveAppendEntriesRequest")
        ((msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)).ev.name == "ReceiveSnapshot")) = true := by
      simp [msgLine, evConv, hname']
    simp only [hn1, ↓reduceIte]
    rw [← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    exact isAER_app C C.length e m.dst s.vote xs m tm hmsg hm hty (by rw [hterm]; exact bt) bmc bi blt bk
  have hcontains : σ.server.contains (idAbs m.dst) = true := by
    rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  have hsm : (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)).stateMatches σ (idAbs m.dst) = true := by
    rw [← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    have := stateMatches_node C s (σ.s (idAbs m.dst)) e m.dst xs hR hs (by rw [hrole]; decide) hterm' hcommit' hrl
      hlog (hxs.trans hin) bt bc bl σ rfl hcontains
    unfold Etcdraft.Line.stateMatches at this ⊢
    simpa [msgLine, nodeLine] using this
  generalize hmabs : (msgAbs C C.length m).get (by simp [msgAbs, hty]) = mabs at *
  have hmt : mabs.type = .appendEntriesRequest := by rw [← hmabs]; simp [msgAbs, hty]
  have hmsub : mabs.subtype = "app" := by rw [← hmabs]; simp [msgAbs, hty]
  have hmterm : mabs.term = uint.Z m.term := by rw [← hmabs]; simp [msgAbs, hty]
  have hmprev : mabs.prevLogIndex = (uint.nat m.index : Nat) := by rw [← hmabs, hidxZ]; simp [msgAbs, hty]
  have hmpt : mabs.prevLogTerm = uint.Z m.logterm := by rw [← hmabs]; simp [msgAbs, hty]
  have hments : mabs.entries = logAbs C C.length (uint.nat m.index + 1) m.entries := by
    rw [← hmabs]; simp [msgAbs, hty]
  have hmsrc : mabs.source = idAbs m.src := by rw [← hmabs]; simp [msgAbs, hty]
  have hmdst : mabs.dest = idAbs m.dst := by rw [← hmabs]; simp [msgAbs, hty]
  apply simRun_snoc_chain C L σ _ e _ hrun hL hparse
  intro lines ts hl hts hl'
  have hlen := parseLines_length _ _ hl
  simp only [List.length_map] at hlen
  have hline := linesTrace_line_last C lines (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) ts.l (by omega)
  obtain ⟨tl, tsl, tpl⟩ := ts
  simp only at hts hl'
  subst hts hl'
  refine ⟨⟨doneSt (truncSt tl (idAbs m.dst) (idAbs m.src) (logAbs C C.length 1 es')) mabs (uint.nat m.index)
    m.entries.length, L.length + 1 + 1, L.length + 1⟩, rfl, ?_⟩
  rw [← hmsrc, ← hmdst]
  rw [← hmsrc, ← hmdst] at hinvT hinvA hinvD
  apply chain_appAccept (linesTrace C (lines ++ [msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)])) (L.length + 1) tpl tl mabs C C.length (uint.nat m.index) m.logterm lastnewi (toPState s).log m.entries es' []
    (by simp) (by omega) (by simp [linesTrace, Etcdraft.Trace.len]; omega)
    (by simp only [linesTrace]; simpa using hboot lines _ hl)
    (by rw [hline]; simp [msgLine, evConv, hname']; rfl) hnd hmem hcnt (by rw [hline]; exact hpred)
    (by unfold Etcdraft.Trace.validatePreStates; rw [hline, hmdst, hsm]; simp)
    (by rw [hline]; exact huniq) (by rw [hmdst]; exact hcontains) hmt
    (by rw [hmdst, hR.2.1]; simp [toPState, hrole, proleRole]; rfl)
    (by rw [hmdst, hR.1, hmterm, hterm]; rfl) hmsub (by rw [hmdst]; exact hR.2.2.2.2.2.1)
    hments hmprev hmpt (fun h => hlt0 h)
    (by rw [hmdst, hR.2.2.2.2.2.2.1, hidxZ]; omega) (fun k x hk hx => hs.2.2 k x (by omega) hx) hbe hwf (by word) hnw happ hinvT hinvA hinvD

theorem oneLess_of_msgs (σ S : Etcdraft.State) (m : Etcdraft.Msg) (h : S.messages = (σ.discard m).messages)
    (hnd : σ.messages.domain.Nodup) (hm : 0 < Etcdraft.Bag.count σ.messages m) :
    Etcdraft.oneLessMessage σ S m = true := by
  have h2 := oneLess_discard σ σ m rfl hnd hm
  unfold Etcdraft.oneLessMessage at h2 ⊢
  rw [h]; exact h2

/-- **A one-round receive line of an append request or heartbeat at a follower** (generic): the
event of raft's receipt of `m` at its `Step`, the line matching `msgAbs m` (`hpred`), its one
successor `S` consuming it. -/
theorem simRun_recvAER1 (C : List w64) (L : List TraceEv) (σ S : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg) (hty : m.ty = .app ∨ m.ty = .heartbeat)
    (hev : SendEvOf (W64 10) m.dst s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : m.dst ∈ C) (hsrv : σ.server = confAbs C)
    (hR : SimServerR C C.length (toPState s) (σ.s (idAbs m.dst))) (hs : LogShapeOk C.length (toPState s))
    (hpre : s.role ≠ .preCandidate)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63)
    (mabs : Etcdraft.Msg) (hmdst : mabs.dest = idAbs m.dst)
    (hpred : recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) mabs = true)
    (hnd : σ.messages.domain.Nodup) (hmem : mabs ∈ σ.messages.domain)
    (hcnt : 0 < Etcdraft.Bag.count σ.messages mabs)
    (huniq : ∀ m' ∈ σ.messages.domain, m' ≠ mabs →
      recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) m' = false)
    (hrcv : σ.receive mabs = .ok [S]) (hmsgs : S.messages = (σ.discard mabs).messages)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinv : S.violated = .ok none) :
    SimRun C (L ++ [e]) S := by
  obtain ⟨hname, hnid, hterm', hvote, hcommit', hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  have hname' : gsStr e.name = "ReceiveAppendEntriesRequest" := by
    simp only [evtNames] at hname
    have : e.name = go!"ReceiveAppendEntriesRequest" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  have hparse : Etcdraft.parseLine L.length (evConv e) =
      .ok (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) := by
    rw [← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    exact parseLine_msg L.length e m.dst s.vote m.src m.dst xs [] tm hnid hvote hconf hmsg hm.2.2.1 hm.2.2.2.1
      (by rw [hm.1]; rcases hty with h | h <;> rw [h] <;> rfl) (by rw [hname']; decide)
  have hcontains : σ.server.contains (idAbs m.dst) = true := by
    rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  apply simRun_recv1 C L σ S hrun hL e _ mabs hparse (by simp [msgLine, evConv, hname']; rfl) hnd hmem hpred
  · rw [hmdst, ← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    have hsm := stateMatches_node C s (σ.s (idAbs m.dst)) e m.dst xs hR hs hpre hterm' hcommit' hrl
      hlog (hxs.trans hin) bt bc bl σ rfl hcontains
    unfold Etcdraft.Line.stateMatches at hsm ⊢
    simpa [msgLine, nodeLine] using hsm
  · intro lines ts _ m' hm' hne; simp [huniq m' hm' hne]
  · exact hrcv
  · exact oneLess_of_msgs σ S mabs hmsgs hnd hcnt
  · exact hboot
  · exact hinv

/-- The specification's state after a heartbeat's receive line. -/
def hbRecvSt (σ : Etcdraft.State) (mabs : Etcdraft.Msg) : Etcdraft.State :=
  withLead ((σ.commitTo mabs.dest mabs.commitIndex).reply { type := .appendEntriesResponse, subtype := "heartbeat", term := (σ.s mabs.dest).currentTerm, success := true, matchIndex := 0, source := mabs.dest, dest := mabs.source } mabs) mabs.dest mabs.source

/-- **A heartbeat's receive line's step** (at a follower of its term, raft's `heartbeat`). -/
theorem simRun_recvHeartbeat (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg) (hty : m.ty = .heartbeat)
    (hev : SendEvOf (W64 10) m.dst s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : m.dst ∈ C) (hsrv : σ.server = confAbs C)
    (hR : SimServerR C C.length (toPState s) (σ.s (idAbs m.dst))) (hs : LogShapeOk C.length (toPState s))
    (hrole : s.role = .follower) (hterm : m.term = s.term) (hents : m.entries = [])
    (hc1 : 1 ≤ uint.Z (toPState s).commit)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (bmc : uint.Z m.commit < 2 ^ 63)
    (hnd : σ.messages.domain.Nodup)
    (hmem : (msgAbs C C.length m).get (by simp [msgAbs, hty]) ∈ σ.messages.domain)
    (hcnt : 0 < Etcdraft.Bag.count σ.messages ((msgAbs C C.length m).get (by simp [msgAbs, hty])))
    (huniq : ∀ m' ∈ σ.messages.domain, m' ≠ (msgAbs C C.length m).get (by simp [msgAbs, hty]) →
      recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) m' = false)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinv : (hbRecvSt σ ((msgAbs C C.length m).get (by simp [msgAbs, hty]))).violated = .ok none) :
    SimRun C (L ++ [e]) (hbRecvSt σ ((msgAbs C C.length m).get (by simp [msgAbs, hty]))) := by
  have hev' := hev
  obtain ⟨-, -, -, -, -, -, -, ⟨xs, ys, hxs, hys, -⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev'
  generalize hmabs : (msgAbs C C.length m).get (by simp [msgAbs, hty]) = mabs at *
  have hmt : mabs.type = .appendEntriesRequest := by rw [← hmabs]; simp [msgAbs, hty]
  have hmsub : mabs.subtype = "heartbeat" := by rw [← hmabs]; simp [msgAbs, hty]
  have hmterm : mabs.term = uint.Z m.term := by rw [← hmabs]; simp [msgAbs, hty]
  have hmprev : mabs.prevLogIndex = 0 := by rw [← hmabs]; simp [msgAbs, hty]
  have hments : mabs.entries = [] := by rw [← hmabs]; simp [msgAbs, hty]
  have hmdst : mabs.dest = idAbs m.dst := by rw [← hmabs]; simp [msgAbs, hty]
  have hcontains : σ.server.contains (idAbs m.dst) = true := by
    rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  apply simRun_recvAER1 C L σ (hbRecvSt σ mabs) hrun hL e s cfg m (Or.inr hty) hev hin hout hC hsrv hR hs
    (by rw [hrole]; decide) bt bc bl mabs hmdst _ hnd hmem hcnt huniq _ (by rfl) hboot hinv
  · unfold recvPred
    have hn1 : (or ((msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)).ev.name == "ReceiveAppendEntriesRequest")
        ((msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)).ev.name == "ReceiveSnapshot")) = true := by
      have hname := hev.1
      simp only [evtNames] at hname
      have : e.name = go!"ReceiveAppendEntriesRequest" := by have := hname; simp at this; exact this.symm
      have hg : gsStr (go!"ReceiveAppendEntriesRequest") = "ReceiveAppendEntriesRequest" := rfl
      simp [msgLine, evConv, this, hg]
    simp only [hn1, ↓reduceIte]
    rw [← hmabs, ← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    exact isAER_heartbeat C C.length e m.dst s.vote xs m tm hmsg hm hty hents (by rw [hterm]; exact bt) bmc
  · have := receive_heartbeat σ mabs (by rw [hmdst]; exact hcontains) hmt
      (by rw [hmdst, hR.2.1]; simp [toPState, hrole, proleRole]; rfl)
      (by rw [hmdst, hR.1, hmterm, hterm]; rfl) hmsub hmprev hments
      (by rw [hmdst, hR.2.2.2.2.2.2.1]; omega)
    rw [this]; rfl

/-- The specification's state after a stale append request's receive line. -/
def staleRecvSt (σ : Etcdraft.State) (mabs : Etcdraft.Msg) : Etcdraft.State :=
  withLead (σ.reply { type := .appendEntriesResponse, subtype := mabs.subtype, term := (σ.s mabs.dest).currentTerm, success := true, matchIndex := (σ.s mabs.dest).commitIndex, source := mabs.dest, dest := mabs.source } mabs) mabs.dest mabs.source

/-- **A stale append request's receive line's step** (raft's `appStale`: its index below the commit
index, the log matching its previous entry). -/
theorem simRun_recvStale (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg) (hty : m.ty = .app)
    (hev : SendEvOf (W64 10) m.dst s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : m.dst ∈ C) (hsrv : σ.server = confAbs C)
    (hR : SimServerR C C.length (toPState s) (σ.s (idAbs m.dst))) (hs : LogShapeOk C.length (toPState s))
    (hrole : s.role = .follower) (hterm : m.term = s.term)
    (hst : uint.Z m.index < uint.Z (toPState s).commit)
    (hmt0 : PlogMatches (entryID.mk (W64 0) (W64 0)) (toPState s).log (entryID.mk m.logterm (W64 (uint.nat m.index))))
    (hlt0 : uint.nat m.index = 0 → m.logterm = W64 0)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (bmc : uint.Z m.commit < 2 ^ 63)
    (bi : uint.Z m.index < 2 ^ 63) (blt : uint.Z m.logterm < 2 ^ 63) (bk : m.entries.length < 2 ^ 63)
    (hnd : σ.messages.domain.Nodup)
    (hmem : (msgAbs C C.length m).get (by simp [msgAbs, hty]) ∈ σ.messages.domain)
    (hcnt : 0 < Etcdraft.Bag.count σ.messages ((msgAbs C C.length m).get (by simp [msgAbs, hty])))
    (huniq : ∀ m' ∈ σ.messages.domain, m' ≠ (msgAbs C C.length m).get (by simp [msgAbs, hty]) →
      recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) m' = false)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinv : (staleRecvSt σ ((msgAbs C C.length m).get (by simp [msgAbs, hty]))).violated = .ok none) :
    SimRun C (L ++ [e]) (staleRecvSt σ ((msgAbs C C.length m).get (by simp [msgAbs, hty]))) := by
  have hev' := hev
  obtain ⟨-, -, -, -, -, -, -, ⟨xs, ys, hxs, hys, -⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev'
  generalize hmabs : (msgAbs C C.length m).get (by simp [msgAbs, hty]) = mabs at *
  have hmt : mabs.type = .appendEntriesRequest := by rw [← hmabs]; simp [msgAbs, hty]
  have hmsub : mabs.subtype = "app" := by rw [← hmabs]; simp [msgAbs, hty]
  have hmterm : mabs.term = uint.Z m.term := by rw [← hmabs]; simp [msgAbs, hty]
  have hidxZ : ((uint.nat m.index : Nat) : Int) = uint.Z m.index := by word
  have hmprev : mabs.prevLogIndex = (uint.nat m.index : Nat) := by rw [← hmabs, hidxZ]; simp [msgAbs, hty]
  have hmpt : mabs.prevLogTerm = uint.Z m.logterm := by rw [← hmabs]; simp [msgAbs, hty]
  have hmdst : mabs.dest = idAbs m.dst := by rw [← hmabs]; simp [msgAbs, hty]
  have hcontains : σ.server.contains (idAbs m.dst) = true := by
    rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  apply simRun_recvAER1 C L σ (staleRecvSt σ mabs) hrun hL e s cfg m (Or.inl hty) hev hin hout hC hsrv hR hs
    (by rw [hrole]; decide) bt bc bl mabs hmdst _ hnd hmem hcnt huniq _ (by rfl) hboot hinv
  · unfold recvPred
    have hn1 : (or ((msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)).ev.name == "ReceiveAppendEntriesRequest")
        ((msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)).ev.name == "ReceiveSnapshot")) = true := by
      have hname := hev.1
      simp only [evtNames] at hname
      have : e.name = go!"ReceiveAppendEntriesRequest" := by have := hname; simp at this; exact this.symm
      have hg : gsStr (go!"ReceiveAppendEntriesRequest") = "ReceiveAppendEntriesRequest" := rfl
      simp [msgLine, evConv, this, hg]
    simp only [hn1, ↓reduceIte]
    rw [← hmabs, ← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    exact isAER_app C C.length e m.dst s.vote xs m tm hmsg hm hty (by rw [hterm]; exact bt) bmc bi blt bk
  · have hlok : LogOkL mabs (σ.s mabs.dest).log = true := by
      rw [hmdst, hR.2.2.2.2.2.1, logOkL_abs C C.length mabs _ (uint.nat m.index) m.logterm hmprev hmpt
        (fun k x hk hx => hs.2.2 k x (by omega) hx) hlt0 (by word), decide_eq_true_iff]
      exact hmt0
    have := receive_appStale σ mabs (by rw [hmdst]; exact hcontains) hmt
      (by rw [hmdst, hR.2.1]; simp [toPState, hrole, proleRole]; rfl)
      (by rw [hmdst, hR.1, hmterm, hterm]; rfl) hmsub
      (by rw [hmdst, hR.2.2.2.2.2.2.1, hmprev, hidxZ]; omega) hlok
    rw [this]; rfl

/-- The specification's state after a rejected append request's receive line. -/
def rejRecvSt (σ : Etcdraft.State) (mabs : Etcdraft.Msg) : Etcdraft.State :=
  withLead (σ.reply { type := .appendEntriesResponse, subtype := "app", term := (σ.s mabs.dest).currentTerm, success := false, matchIndex := 0, source := mabs.dest, dest := mabs.source } mabs) mabs.dest mabs.source

/-- **A rejected append request's receive line's step** (raft's `appReject`: the log not matching
its previous entry; pre-vote and check-quorum off). -/
theorem simRun_recvReject (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg) (hty : m.ty = .app)
    (hev : SendEvOf (W64 10) m.dst s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : m.dst ∈ C) (hsrv : σ.server = confAbs C)
    (hR : SimServerR C C.length (toPState s) (σ.s (idAbs m.dst))) (hs : LogShapeOk C.length (toPState s))
    (hrole : s.role = .follower) (hterm : m.term = s.term) (hpv : σ.preVote = false) (hcq : σ.checkQuorum = false)
    (hmt0 : ¬ PlogMatches (entryID.mk (W64 0) (W64 0)) (toPState s).log (entryID.mk m.logterm (W64 (uint.nat m.index))))
    (hlt0 : uint.nat m.index = 0 → m.logterm = W64 0)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (bmc : uint.Z m.commit < 2 ^ 63)
    (bi : uint.Z m.index < 2 ^ 63) (blt : uint.Z m.logterm < 2 ^ 63) (bk : m.entries.length < 2 ^ 63)
    (hnd : σ.messages.domain.Nodup)
    (hmem : (msgAbs C C.length m).get (by simp [msgAbs, hty]) ∈ σ.messages.domain)
    (hcnt : 0 < Etcdraft.Bag.count σ.messages ((msgAbs C C.length m).get (by simp [msgAbs, hty])))
    (huniq : ∀ m' ∈ σ.messages.domain, m' ≠ (msgAbs C C.length m).get (by simp [msgAbs, hty]) →
      recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) m' = false)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinv : (rejRecvSt σ ((msgAbs C C.length m).get (by simp [msgAbs, hty]))).violated = .ok none) :
    SimRun C (L ++ [e]) (rejRecvSt σ ((msgAbs C C.length m).get (by simp [msgAbs, hty]))) := by
  have hev' := hev
  obtain ⟨-, -, -, -, -, -, -, ⟨xs, ys, hxs, hys, -⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev'
  generalize hmabs : (msgAbs C C.length m).get (by simp [msgAbs, hty]) = mabs at *
  have hmt : mabs.type = .appendEntriesRequest := by rw [← hmabs]; simp [msgAbs, hty]
  have hmterm : mabs.term = uint.Z m.term := by rw [← hmabs]; simp [msgAbs, hty]
  have hidxZ : ((uint.nat m.index : Nat) : Int) = uint.Z m.index := by word
  have hmprev : mabs.prevLogIndex = (uint.nat m.index : Nat) := by rw [← hmabs, hidxZ]; simp [msgAbs, hty]
  have hmpt : mabs.prevLogTerm = uint.Z m.logterm := by rw [← hmabs]; simp [msgAbs, hty]
  have hmdst : mabs.dest = idAbs m.dst := by rw [← hmabs]; simp [msgAbs, hty]
  have hcontains : σ.server.contains (idAbs m.dst) = true := by
    rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  apply simRun_recvAER1 C L σ (rejRecvSt σ mabs) hrun hL e s cfg m (Or.inl hty) hev hin hout hC hsrv hR hs
    (by rw [hrole]; decide) bt bc bl mabs hmdst _ hnd hmem hcnt huniq _ (by rfl) hboot hinv
  · unfold recvPred
    have hn1 : (or ((msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)).ev.name == "ReceiveAppendEntriesRequest")
        ((msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)).ev.name == "ReceiveSnapshot")) = true := by
      have hname := hev.1
      simp only [evtNames] at hname
      have : e.name = go!"ReceiveAppendEntriesRequest" := by have := hname; simp at this; exact this.symm
      have hg : gsStr (go!"ReceiveAppendEntriesRequest") = "ReceiveAppendEntriesRequest" := rfl
      simp [msgLine, evConv, this, hg]
    simp only [hn1, ↓reduceIte]
    rw [← hmabs, ← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    exact isAER_app C C.length e m.dst s.vote xs m tm hmsg hm hty (by rw [hterm]; exact bt) bmc bi blt bk
  · have hlok : LogOkL mabs (σ.s mabs.dest).log = false := by
      rw [hmdst, hR.2.2.2.2.2.1, logOkL_abs C C.length mabs _ (uint.nat m.index) m.logterm hmprev hmpt
        (fun k x hk hx => hs.2.2 k x (by omega) hx) hlt0 (by word)]
      exact decide_eq_false hmt0
    have := receive_appReject σ mabs (by rw [hmdst]; exact hcontains) hmt
      (by rw [hmdst, hR.2.1]; simp [toPState, hrole, proleRole]; rfl)
      (by rw [hmdst, hR.1, hmterm, hterm]; rfl) hpv hcq hlok
    rw [this]; rfl

/-- **An append response's line predicate**, accepting or rejecting. -/
theorem isAEResp_any (C : List w64) (bl : Nat) (e : TraceEv) (id vote : w64) (xs : List w64) (m : Msg)
    (tm : TraceMsg) (hmsg : e.msg = some tm) (hm : MsgEvOf m tm) (hty : m.ty = .appResp)
    (bt : uint.Z m.term < 2 ^ 63) (bi : uint.Z m.index < 2 ^ 63) :
    (msgLine e id vote m.src m.dst xs).isAppendEntriesResponse
      ((msgAbs C bl m).get (by simp [msgAbs, hty])) = true := by
  obtain ⟨htyp, hterm, -, -, -, -, hidx, -, hrej'⟩ := hm
  simp only [msgAbs, hty, Option.get_some]
  unfold Etcdraft.Line.isAppendEntriesResponse
  simp only [msgLine, evConv, hmsg, Option.map_some]
  rw [htyp, hty, hterm, hidx, hrej', gInt_of_lt _ bt, gInt_of_lt _ bi, gsStr_msgTypeStr_appResp]
  cases m.reject <;> simp [Etcdraft.raftMsgType, Etcdraft.raftMsgSubtype]

/-- **A one-round receive line's step for any message** (generic): the event of raft's receipt of `m`
at its `Step` (the receive name `nm`), the line matching `msgAbs m`, its one successor `S` consuming
it. -/
theorem simRun_recvMsg1 (C : List w64) (L : List TraceEv) (σ S : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg) (evt : w64) (nm : String)
    (hev : SendEvOf evt m.dst s cfg m e) (hname' : gsStr e.name = nm)
    (hrecvnm : Etcdraft.isReceiveName nm = true)
    (htyp : (Etcdraft.raftMsgType (gsStr (msgTypeStr m.ty))).isSome = true)
    (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : m.dst ∈ C) (hsrv : σ.server = confAbs C)
    (hR : SimServerR C C.length (toPState s) (σ.s (idAbs m.dst))) (hs : LogShapeOk C.length (toPState s))
    (hpre : s.role ≠ .preCandidate)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63)
    (mabs : Etcdraft.Msg) (hmdst : mabs.dest = idAbs m.dst)
    (hpred : recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) mabs = true)
    (hnd : σ.messages.domain.Nodup) (hmem : mabs ∈ σ.messages.domain)
    (hcnt : 0 < Etcdraft.Bag.count σ.messages mabs)
    (huniq : ∀ m' ∈ σ.messages.domain, m' ≠ mabs →
      recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) m' = false)
    (hrcv : σ.receive mabs = .ok [S]) (hmsgs : S.messages = (σ.discard mabs).messages)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinv : S.violated = .ok none) :
    SimRun C (L ++ [e]) S := by
  obtain ⟨-, hnid, hterm', hvote, hcommit', hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  have hparse : Etcdraft.parseLine L.length (evConv e) =
      .ok (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) := by
    rw [← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    exact parseLine_msg L.length e m.dst s.vote m.src m.dst xs [] tm hnid hvote hconf hmsg hm.2.2.1 hm.2.2.2.1
      (by rw [hm.1]; exact htyp)
      (by rw [hname']; intro h; rw [h] at hrecvnm; exact absurd hrecvnm (by decide))
  have hcontains : σ.server.contains (idAbs m.dst) = true := by
    rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  apply simRun_recv1 C L σ S hrun hL e _ mabs hparse (by simp only [msgLine, evConv]; rw [hname']; exact hrecvnm)
    hnd hmem hpred
  · rw [hmdst, ← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    have hsm := stateMatches_node C s (σ.s (idAbs m.dst)) e m.dst xs hR hs hpre hterm' hcommit' hrl
      hlog (hxs.trans hin) bt bc bl σ rfl hcontains
    unfold Etcdraft.Line.stateMatches at hsm ⊢
    simpa [msgLine, nodeLine] using hsm
  · intro lines ts _ m' hm' hne; simp [huniq m' hm' hne]
  · exact hrcv
  · exact oneLess_of_msgs σ S mabs hmsgs hnd hcnt
  · exact hboot
  · exact hinv

theorem recvPred_aer (ln : Etcdraft.Line) (m : Etcdraft.Msg) (h : ln.ev.name = "ReceiveAppendEntriesRequest") :
    recvPred ln m = ln.isAppendEntriesRequest m := by unfold recvPred; simp [h]

theorem recvPred_aeresp (ln : Etcdraft.Line) (m : Etcdraft.Msg) (h : ln.ev.name = "ReceiveAppendEntriesResponse") :
    recvPred ln m = ln.isAppendEntriesResponse m := by unfold recvPred; simp [h]

theorem recvPred_rvreq (ln : Etcdraft.Line) (m : Etcdraft.Msg) (h : ln.ev.name = "ReceiveRequestVoteRequest") :
    recvPred ln m = ln.isRequestVoteRequest m := by unfold recvPred; simp [h]

theorem recvPred_rvresp (ln : Etcdraft.Line) (m : Etcdraft.Msg) (h : ln.ev.name = "ReceiveRequestVoteResponse") :
    recvPred ln m = ln.isRequestVoteResponse m := by unfold recvPred; simp [h]

theorem msgLine_name (e : TraceEv) (id vote f d : w64) (xs : List w64) :
    (msgLine e id vote f d xs).ev.name = gsStr e.name := rfl

/-- The receive event names, from the event constant. -/
theorem recvName_of (evt : w64) (e : TraceEv) (h : evtNames[uint.nat evt]? = some e.name) :
    (evt = W64 10 → gsStr e.name = "ReceiveAppendEntriesRequest") ∧
    (evt = W64 12 → gsStr e.name = "ReceiveAppendEntriesResponse") ∧
    (evt = W64 14 → gsStr e.name = "ReceiveRequestVoteRequest") ∧
    (evt = W64 16 → gsStr e.name = "ReceiveRequestVoteResponse") := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hev <;> subst hev <;> simp only [evtNames] at h <;>
    (have := h; simp at this; rw [← this]; rfl)

/-- **A lower-term response's receive line's step** (raft ignores it; the specification drops it). -/
theorem simRun_recvStaleResp (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg) (evt : w64)
    (htyev : (m.ty = .appResp ∧ evt = W64 12) ∨ (m.ty = .voteResp ∧ evt = W64 16))
    (hev : SendEvOf evt m.dst s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : m.dst ∈ C) (hsrv : σ.server = confAbs C)
    (hR : SimServerR C C.length (toPState s) (σ.s (idAbs m.dst))) (hs : LogShapeOk C.length (toPState s))
    (hpre : s.role ≠ .preCandidate) (hlt : uint.Z m.term < uint.Z s.term)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (bi : uint.Z m.index < 2 ^ 63)
    (mabs : Etcdraft.Msg) (hmabs : msgAbs C C.length m = some mabs)
    (hnd : σ.messages.domain.Nodup) (hmem : mabs ∈ σ.messages.domain)
    (hcnt : 0 < Etcdraft.Bag.count σ.messages mabs)
    (huniq : ∀ m' ∈ σ.messages.domain, m' ≠ mabs →
      recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) m' = false)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinv : (σ.discard mabs).violated = .ok none) :
    SimRun C (L ++ [e]) (σ.discard mabs) := by
  have hev' := hev
  obtain ⟨hname, -, -, -, -, -, -, ⟨xs, ys, hxs, -, -⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev'
  have hnames := recvName_of evt e hname
  have hcontains : σ.server.contains (idAbs m.dst) = true := by
    rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  rcases htyev with ⟨hty, rfl⟩ | ⟨hty, rfl⟩
  · have hmt : mabs.type = .appendEntriesResponse := by
      simp [msgAbs, hty] at hmabs; rw [← hmabs]
    have hmdst : mabs.dest = idAbs m.dst := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
    have hmterm : mabs.term = uint.Z m.term := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
    have hname' := hnames.2.1 rfl
    apply simRun_recvMsg1 C L σ _ hrun hL e s cfg m _ _ hev hname' (by rfl) (by rw [hty]; rfl) hin hout hC hsrv hR hs
      hpre bt bc bl mabs hmdst _ hnd hmem hcnt huniq _ (by rfl) hboot hinv
    · rw [recvPred_aeresp _ _ (by rw [msgLine_name, hname'])]
      have := isAEResp_any C C.length e m.dst s.vote (elements cfg.incoming) m tm hmsg hm hty (by omega) bi
      simp only [hmabs, Option.get_some] at this; exact this
    · exact receive_staleResp σ mabs (by rw [hmdst]; exact hcontains) (Or.inl hmt)
        (by rw [hmdst, hR.1, hmterm]; exact hlt)
  · have hmt : mabs.type = .requestVoteResponse := by
      simp [msgAbs, hty] at hmabs; rw [← hmabs]
    have hmdst : mabs.dest = idAbs m.dst := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
    have hmterm : mabs.term = uint.Z m.term := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
    have hname' := hnames.2.2.2 rfl
    apply simRun_recvMsg1 C L σ _ hrun hL e s cfg m _ _ hev hname' (by rfl) (by rw [hty]; rfl) hin hout hC hsrv hR hs
      hpre bt bc bl mabs hmdst _ hnd hmem hcnt huniq _ (by rfl) hboot hinv
    · rw [recvPred_rvresp _ _ (by rw [msgLine_name, hname'])]
      have := isRVResp_voteResp C C.length e m.dst s.vote (elements cfg.incoming) m tm hmsg hm hty (by omega)
      simp only [hmabs, Option.get_some] at this; exact this
    · exact receive_staleResp σ mabs (by rw [hmdst]; exact hcontains) (Or.inr hmt)
        (by rw [hmdst, hR.1, hmterm]; exact hlt)

/-- The specification's phantom reply to a lower-term request. -/
def phantomReply (σ : Etcdraft.State) (mabs : Etcdraft.Msg) : Etcdraft.Msg :=
  if mabs.type = .requestVoteRequest then
    { type := .requestVoteResponse, term := (σ.s mabs.dest).currentTerm, voteGranted := false, source := mabs.dest, dest := mabs.source }
  else
    { type := .appendEntriesResponse, subtype := "app", term := (σ.s mabs.dest).currentTerm, success := false, matchIndex := 0, source := mabs.dest, dest := mabs.source }

/-- **A lower-term request's receive line's step** (raft ignores it, pre-vote and check-quorum off;
the specification answers it with a phantom). -/
theorem simRun_recvStaleReq (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg) (evt : w64)
    (htyev : (m.ty = .app ∧ evt = W64 10) ∨ (m.ty = .vote ∧ evt = W64 14))
    (hev : SendEvOf evt m.dst s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : m.dst ∈ C) (hsrv : σ.server = confAbs C) (hpv : σ.preVote = false) (hcq : σ.checkQuorum = false)
    (hR : SimServerR C C.length (toPState s) (σ.s (idAbs m.dst))) (hs : LogShapeOk C.length (toPState s))
    (hpre : s.role ≠ .preCandidate) (hlt : uint.Z m.term < uint.Z s.term)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (bi : uint.Z m.index < 2 ^ 63)
    (blt : uint.Z m.logterm < 2 ^ 63) (bk : m.entries.length < 2 ^ 63) (bmc : uint.Z m.commit < 2 ^ 63)
    (mabs : Etcdraft.Msg) (hmabs : msgAbs C C.length m = some mabs)
    (hnd : σ.messages.domain.Nodup) (hmem : mabs ∈ σ.messages.domain)
    (hcnt : 0 < Etcdraft.Bag.count σ.messages mabs)
    (huniq : ∀ m' ∈ σ.messages.domain, m' ≠ mabs →
      recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) m' = false)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinv : (σ.reply (phantomReply σ mabs) mabs).violated = .ok none) :
    SimRun C (L ++ [e]) (σ.reply (phantomReply σ mabs) mabs) := by
  have hev' := hev
  obtain ⟨hname, -, -, -, -, -, -, -, ⟨tm, hmsg, hm⟩, -⟩ := hev'
  have hnames := recvName_of evt e hname
  have hcontains : σ.server.contains (idAbs m.dst) = true := by
    rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  rcases htyev with ⟨hty, rfl⟩ | ⟨hty, rfl⟩
  · have hmt : mabs.type = .appendEntriesRequest := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
    have hmdst : mabs.dest = idAbs m.dst := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
    have hmterm : mabs.term = uint.Z m.term := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
    have hname' := hnames.1 rfl
    have hph : phantomReply σ mabs = { type := .appendEntriesResponse, subtype := "app", term := (σ.s mabs.dest).currentTerm, success := false, matchIndex := 0, source := mabs.dest, dest := mabs.source } := by
      unfold phantomReply; simp [hmt]
    apply simRun_recvMsg1 C L σ _ hrun hL e s cfg m _ _ hev hname' (by rfl) (by rw [hty]; rfl) hin hout hC hsrv hR hs
      hpre bt bc bl mabs hmdst _ hnd hmem hcnt huniq _ (by rfl) hboot hinv
    · rw [recvPred_aer _ _ (by rw [msgLine_name, hname'])]
      have := isAER_app C C.length e m.dst s.vote (elements cfg.incoming) m tm hmsg hm hty (by omega) bmc bi blt bk
      simp only [hmabs, Option.get_some] at this; exact this
    · rw [hph]
      exact receive_staleAER σ mabs (by rw [hmdst]; exact hcontains) hmt (by rw [hmdst, hR.1, hmterm]; exact hlt) hpv hcq
  · have hmt : mabs.type = .requestVoteRequest := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
    have hmdst : mabs.dest = idAbs m.dst := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
    have hmterm : mabs.term = uint.Z m.term := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
    have hname' := hnames.2.2.1 rfl
    have hph : phantomReply σ mabs = { type := .requestVoteResponse, term := (σ.s mabs.dest).currentTerm, voteGranted := false, source := mabs.dest, dest := mabs.source } := by
      unfold phantomReply; simp [hmt]
    apply simRun_recvMsg1 C L σ _ hrun hL e s cfg m _ _ hev hname' (by rfl) (by rw [hty]; rfl) hin hout hC hsrv hR hs
      hpre bt bc bl mabs hmdst _ hnd hmem hcnt huniq _ (by rfl) hboot hinv
    · rw [recvPred_rvreq _ _ (by rw [msgLine_name, hname'])]
      have := isRVReq_vote C C.length e m.dst s.vote (elements cfg.incoming) m tm hmsg hm hty (by omega) bi blt
      simp only [hmabs, Option.get_some] at this; exact this
    · rw [hph]
      exact receive_staleVoteReq σ mabs (by rw [hmdst]; exact hcontains) hmt (by rw [hmdst, hR.1, hmterm]; exact hlt)

/-- **A two-round receive line's step** (generic: `UpdateTerm`, then a one-round handler at the new
term): from a run reaching `σ`, the line `ln` matching `mabs`, the first round's successor `U` keeping
it (of another term at its receiver), the second's `S` consuming it. -/
theorem simRun_recv2 (C : List w64) (L : List TraceEv) (σ U S : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (ln : Etcdraft.Line) (mabs : Etcdraft.Msg)
    (hparse : Etcdraft.parseLine L.length (evConv e) = .ok ln)
    (hrecv : Etcdraft.isReceiveName ln.ev.name = true)
    (hnd : σ.messages.domain.Nodup) (hmem : mabs ∈ σ.messages.domain)
    (hcnt : 0 < Etcdraft.Bag.count σ.messages mabs)
    (hmatch : recvPred ln mabs = true) (hpre : ln.stateMatches σ mabs.dest = true)
    (huniq : ∀ m' ∈ σ.messages.domain, m' ≠ mabs → recvPred ln m' = false)
    (hdest : mabs.dest ∈ σ.server)
    (hrcv1 : σ.receive mabs = .ok [U]) (hU : U.messages = σ.messages) (hUs : U.server = σ.server)
    (hUt : (U.s mabs.dest).currentTerm ≠ (σ.s mabs.dest).currentTerm)
    (hrcv2 : U.receive mabs = .ok [S]) (hmsgs : S.messages = (U.discard mabs).messages)
    (hboot : ∀ lines ln', parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln'])).getD L.length false = false)
    (hinvU : U.violated = .ok none) (hinv : S.violated = .ok none) :
    SimRun C (L ++ [e]) S := by
  apply simRun_snoc_chain C L σ _ e _ hrun hL hparse
  intro lines ts hl hts hl'
  have hlen := parseLines_length _ _ hl
  simp only [List.length_map] at hlen
  have hline := linesTrace_line_last C lines ln ts.l (by omega)
  obtain ⟨tl, tsl, tpl⟩ := ts
  simp only at hts hl'
  subst hts hl'
  refine ⟨⟨S, L.length + 1 + 1, L.length + 1⟩, rfl, ?_⟩
  have hb : (linesTrace C (lines ++ [ln])).bootstrap.getD (L.length + 1 - 1) false = false := by
    simp only [linesTrace]; simpa using hboot lines _ hl
  have hone1 : Etcdraft.oneLessMessage tl U mabs = false := by
    unfold Etcdraft.oneLessMessage; rw [hU]; simp; intro h; rw [h]; decide
  have hone2 : Etcdraft.oneLessMessage U S mabs = true :=
    oneLess_of_msgs U S mabs hmsgs (by rw [hU]; exact hnd) (by rw [hU]; exact hcnt)
  apply Chain.step _ _ ⟨U, L.length + 1, L.length + 1⟩ _ _ rfl
    (memEq_false_of_logs_or_term _ _ mabs.dest (by
      intro v hv; simp only [List.mem_singleton] at hv; subst hv
      exact ⟨hdest, Or.inr (fun h => hUt h.symm)⟩)) hinvU
  · refine Chain.last _ ⟨U, L.length + 1, L.length + 1⟩ ⟨S, L.length + 1 + 1, L.length + 1⟩ ?_ rfl hinv
    have := next_receive (linesTrace C (lines ++ [ln])) ⟨U, L.length + 1, L.length + 1⟩ mabs S (by simp)
      (by simp [linesTrace, Etcdraft.Trace.len]; omega) hb (by rw [hline]; exact hrecv)
      (by rw [hU]; exact hnd) (by rw [hU]; exact hmem) (by rw [hline]; exact hmatch)
      (validatePre_later _ _ (by omega) _ _)
      (fun m' hm' hne => by rw [hU] at hm'; rw [hline]; simp [huniq m' hm' hne]) hrcv2
    rw [this]; simp [recvNext, hone2]
  · have := next_receive (linesTrace C (lines ++ [ln])) ⟨tl, L.length + 1, tpl⟩ mabs U (by simp)
      (by simp [linesTrace, Etcdraft.Trace.len]; omega) hb (by rw [hline]; exact hrecv) hnd hmem
      (by rw [hline]; exact hmatch)
      (by unfold Etcdraft.Trace.validatePreStates; rw [hline, hpre]; simp)
      (fun m' hm' hne => by rw [hline]; simp [huniq m' hm' hne]) hrcv1
    rw [this]; simp [recvNext, hone1]

end TraceSim

end EtcdGrove
end Perennial
