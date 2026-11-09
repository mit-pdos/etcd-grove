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

end TraceSim

end EtcdGrove
end Perennial
