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

end TraceSim

end EtcdGrove
end Perennial
