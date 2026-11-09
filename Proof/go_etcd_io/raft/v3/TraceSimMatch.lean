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

end TraceSim

end EtcdGrove
end Perennial
