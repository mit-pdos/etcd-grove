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
    (hboot : ∀ lines, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [nodeLine e id vote xs])).getD L.length false = false)
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
  · simp only [linesTrace]; rw [hl']; simpa using hboot lines hl
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
    (by rw [hname']; rfl) (by rw [hname']; decide) (fun lines hl => hboot lines _ hl) _ hinv
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
    (by rw [hname']; rfl) (by rw [hname']; decide) (fun lines hl => hboot lines _ hl) _ hinv
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
    (by rw [hname']; rfl) (by rw [hname']; decide) (fun lines hl => hboot lines _ hl) _ hinv
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
    (by rw [hname']; rfl) (by rw [hname']; decide) (fun lines hl => hboot lines _ hl) _ hinv
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

theorem srvKey_truncSt (σ : Etcdraft.State) (i j : Etcdraft.ID) (L : List Etcdraft.Entry) :
    srvKey ((truncSt σ i j L).s i) = srvKey (σ.s i) := by
  simp [srvKey, truncSt, withLead, Etcdraft.State.upd]

/-- **An accepted append request's line, with a conflict** (raft's `maybeAppend` truncating at the
batch's `d`-th entry, `p + d` past the log's start): the specification's rounds from the line's
first state, the truncations down to `p + d`, the append, `AppendEntriesAlreadyDone`, as a chain. -/
theorem chain_appConflict (t : Etcdraft.Trace) (l0 pl0 : Nat) (σ : Etcdraft.State) (mabs : Etcdraft.Msg)
    (C : List w64) (bl p d : Nat) (es ents : List EntryM) (pre : List Etcdraft.TState)
    (hpreT : ∀ v ∈ pre, mabs.dest ∈ v.s.server ∧ srvKey (v.s.s mabs.dest) ≠ srvKey (σ.s mabs.dest))
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
  have hAkey : srvKey (A.s mabs.dest) = srvKey (σ.s mabs.dest) := by simp [srvKey, hAst, hAterm]
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
          exact ⟨hvs, Or.inr (by simp only; rw [srvKey_truncSt]; exact hvt)⟩
        refine ⟨hdestσ, Or.inl ?_⟩
        simp only; rw [hlogN, (hSf _).2.2.2.2.2]; exact logAbs_take_ne C bl es _ _ (Nat.le_refl _) (by omega) (by omega)))
      (hinvT _ (by omega) (by omega))
    have hcd := chain_down t l0 mabs.dest S (fun k => logAbs C bl 1 (es.take k)) (p + d) es.length
      ⟨doneSt A mabs p ents.length, l0 + 1, l0⟩ (srvKey (σ.s mabs.dest)) (fun k => srvKey_truncSt _ _ _ _)
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
            · right; simp only; rw [hAkey]; exact ht))
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
          exact ⟨hvs, Or.inr (by simp only; rw [hAkey]; exact hvt)⟩
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
    (hpreT : ∀ v ∈ pre, mabs.dest ∈ v.s.server ∧ srvKey (v.s.s mabs.dest) ≠ srvKey (σ.s mabs.dest))
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
    (hUt : srvKey (U.s mabs.dest) ≠ srvKey (σ.s mabs.dest))
    (hrcv2 : U.receive mabs = .ok [S]) (hone2 : Etcdraft.oneLessMessage U S mabs = true)
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

/-- **A receive line's first round** at server `i` (`UpdateTerm`, or a candidate's
`ReturnToFollower`): its one successor `U`, fresh (its term or role differs), keeping the servers,
the messages, the commit index and the log, `i` a follower of the message's term. -/
def FirstRound (σ U : Etcdraft.State) (mabs : Etcdraft.Msg) (i : Etcdraft.ID) : Prop :=
  σ.receive mabs = .ok [U] ∧ srvKey (U.s i) ≠ srvKey (σ.s i) ∧
  U.server = σ.server ∧ U.messages = σ.messages ∧ (U.s i).state = Etcdraft.follower ∧
  (U.s i).currentTerm = mabs.term ∧ (U.s i).commitIndex = (σ.s i).commitIndex ∧ (U.s i).log = (σ.s i).log

theorem firstRound_updateTerm (σ : Etcdraft.State) (mabs : Etcdraft.Msg) (i : Etcdraft.ID) (hi : mabs.dest = i)
    (hsrv : σ.server.contains i = true)
    (hty : mabs.type = .requestVoteRequest ∨ mabs.type = .requestVoteResponse ∨ mabs.type = .appendEntriesRequest ∨
      mabs.type = .appendEntriesResponse)
    (hterm : (σ.s i).currentTerm < mabs.term) :
    FirstRound σ (σ.becomeFollowerOfTerm i mabs.term) mabs i := by
  subst hi
  have hUf := becomeFollowerOfTerm_facts σ mabs.dest mabs.term
  exact ⟨receive_updateTerm σ mabs hsrv hty hterm, srvKey_ne_of_term _ _ (by rw [hUf.2.2.2.1]; omega), hUf⟩

/-- `ReturnToFollowerState` at a candidate, with the append request's `lead' = j`. -/
def rtfSt (σ : Etcdraft.State) (i j : Etcdraft.ID) : Etcdraft.State :=
  withLead (σ.upd i (fun v => { v with state := Etcdraft.follower })) i j

theorem firstRound_rtf (σ : Etcdraft.State) (mabs : Etcdraft.Msg) (i : Etcdraft.ID) (hi : mabs.dest = i)
    (hsrv : σ.server.contains i = true) (hty : mabs.type = .appendEntriesRequest)
    (hterm : mabs.term = (σ.s i).currentTerm) (hc : (σ.s i).state = Etcdraft.candidate) :
    FirstRound σ (rtfSt σ i mabs.source) mabs i := by
  subst hi
  have hsrv' : mabs.dest ∈ σ.server := List.contains_iff_mem.1 hsrv
  have hfc : Etcdraft.follower ≠ Etcdraft.candidate := by decide
  refine ⟨?_, srvKey_ne_of_state _ _ (by simp [rtfSt, withLead, Etcdraft.State.upd, hc]; exact hfc),
    by simp [rtfSt, withLead, Etcdraft.State.upd], by simp [rtfSt, withLead, Etcdraft.State.upd],
    by simp [rtfSt, withLead, Etcdraft.State.upd], by simp [rtfSt, withLead, Etcdraft.State.upd, hterm],
    by simp [rtfSt, withLead, Etcdraft.State.upd], by simp [rtfSt, withLead, Etcdraft.State.upd]⟩
  unfold Etcdraft.State.receive
  have hut : σ.updateTerm mabs.dest mabs.source mabs = none := by
    unfold Etcdraft.State.updateTerm; simp [hterm]
  have hh : σ.handleAppendEntriesRequest mabs.dest mabs.source mabs = .ok [rtfSt σ mabs.dest mabs.source] := by
    unfold Etcdraft.State.handleAppendEntriesRequest Etcdraft.State.acceptAppendEntriesRequest
      Etcdraft.State.rejectAppendEntriesRequest Etcdraft.State.returnToFollowerState
    have hcf : ¬ Etcdraft.candidate = Etcdraft.follower := by decide
    simp [hterm, hc, hcf, Etcdraft.somes, pure, Except.pure, bind, Except.bind, rtfSt, withLead]
  simp [hsrv', hty, hut, hh, Etcdraft.somes, pure, Except.pure, bind, Except.bind]

/-- **A higher-term vote request's receive line's step**: `UpdateTerm`, then
`HandleRequestVoteRequest` at the request's term. -/
theorem simRun_recvVoteReqHigher (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg) (hty : m.ty = .vote)
    (hev : SendEvOf (W64 14) m.dst s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : m.dst ∈ C) (hsrv : σ.server = confAbs C)
    (hR : SimServerR C C.length (toPState s) (σ.s (idAbs m.dst))) (hs : LogShapeOk C.length (toPState s))
    (hpre : s.role ≠ .preCandidate) (hgt : uint.Z s.term < uint.Z m.term)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (bi : uint.Z m.index < 2 ^ 63)
    (blt : uint.Z m.logterm < 2 ^ 63) (bmt : uint.Z m.term < 2 ^ 63)
    (mabs : Etcdraft.Msg) (hmabs : msgAbs C C.length m = some mabs)
    (hnd : σ.messages.domain.Nodup) (hmem : mabs ∈ σ.messages.domain)
    (hcnt : 0 < Etcdraft.Bag.count σ.messages mabs)
    (huniq : ∀ m' ∈ σ.messages.domain, m' ≠ mabs →
      recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) m' = false)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinvU : (σ.becomeFollowerOfTerm (idAbs m.dst) mabs.term).violated = .ok none)
    (hinv : (voteReqResult (σ.becomeFollowerOfTerm (idAbs m.dst) mabs.term) (idAbs m.dst) (idAbs m.src)
      mabs).violated = .ok none) :
    SimRun C (L ++ [e]) (voteReqResult (σ.becomeFollowerOfTerm (idAbs m.dst) mabs.term) (idAbs m.dst)
      (idAbs m.src) mabs) := by
  have hev' := hev
  obtain ⟨hname, hnid, hterm', hvote, hcommit', hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev'
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  have hname' := (recvName_of _ e hname).2.2.1 rfl
  have hparse : Etcdraft.parseLine L.length (evConv e) =
      .ok (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) := by
    rw [← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    exact parseLine_msg L.length e m.dst s.vote m.src m.dst xs [] tm hnid hvote hconf hmsg hm.2.2.1 hm.2.2.2.1
      (by rw [hm.1, hty]; rfl) (by rw [hname']; decide)
  have hmt : mabs.type = .requestVoteRequest := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmdst : mabs.dest = idAbs m.dst := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmsrc : mabs.source = idAbs m.src := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmterm : mabs.term = uint.Z m.term := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hcontains : σ.server.contains (idAbs m.dst) = true := by
    rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  have hdest : mabs.dest ∈ σ.server := by rw [hmdst]; exact List.contains_iff_mem.1 hcontains
  have hcur : (σ.s mabs.dest).currentTerm < mabs.term := by rw [hmdst, hR.1, hmterm]; exact hgt
  have hUf := becomeFollowerOfTerm_facts σ mabs.dest mabs.term
  rw [hmdst] at hUf hcur
  apply simRun_recv2 C L σ _ _ hrun hL e _ mabs hparse (by simp only [msgLine, evConv]; rw [hname']; rfl)
    hnd hmem hcnt _ _ huniq hdest
    (by have := receive_updateTerm σ mabs (by rw [hmdst]; exact hcontains) (Or.inl hmt) (by rw [hmdst]; exact hcur)
        rw [hmdst] at this; exact this)
    hUf.2.1 hUf.1 (srvKey_ne_of_term _ _ (by rw [hmdst, hUf.2.2.2.1]; omega)) _
    (oneLess_voteReq _ _ _ mabs (by rw [hUf.2.2.2.1]; omega) (by rw [hUf.2.1]; exact hnd) (by rw [hUf.2.1]; exact hcnt))
    hboot hinvU hinv
  · rw [recvPred_rvreq _ _ (by rw [msgLine_name, hname'])]
    have := isRVReq_vote C C.length e m.dst s.vote (elements cfg.incoming) m tm hmsg hm hty bmt bi blt
    simp only [hmabs, Option.get_some] at this; exact this
  · rw [hmdst, ← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    have hsm := stateMatches_node C s (σ.s (idAbs m.dst)) e m.dst xs hR hs hpre hterm' hcommit' hrl
      hlog (hxs.trans hin) bt bc bl σ rfl hcontains
    unfold Etcdraft.Line.stateMatches at hsm ⊢
    simpa [msgLine, nodeLine] using hsm
  · have := receive_voteReq (σ.becomeFollowerOfTerm (idAbs m.dst) mabs.term) mabs
      (by rw [hmdst, Etcdraft.State.becomeFollowerOfTerm, Etcdraft.State.upd]; exact hcontains) hmt
      (by rw [hmdst, hUf.2.2.2.1])
    rw [this, hmdst, hmsrc]

/-- **A higher-term append request's receive line's step** (raft's `becomeFollower` then
`maybeAppend` succeeding): `UpdateTerm`, then the specification's truncations, append and
`AppendEntriesAlreadyDone` over the new log, at the request's term. -/
theorem simRun_recvAppU (C : List w64) (L : List TraceEv) (σ U : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg)
    (hev : SendEvOf (W64 10) m.dst s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : m.dst ∈ C) (hsrv : σ.server = confAbs C)
    (hR : SimServerR C C.length (toPState s) (σ.s (idAbs m.dst))) (hs : LogShapeOk C.length (toPState s))
    (hpre : s.role ≠ .preCandidate) (hty : m.ty = .app)
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
    (bmt : uint.Z m.term < 2 ^ 63)
    (hnw : (uint.nat m.index : Int) + m.entries.length + 1 < 2 ^ 64)
    (mabs : Etcdraft.Msg) (hmabs : msgAbs C C.length m = some mabs)
    (hFR : FirstRound σ U mabs (idAbs m.dst))
    (hnd : σ.messages.domain.Nodup) (hmem : mabs ∈ σ.messages.domain)
    (hcnt : 0 < Etcdraft.Bag.count σ.messages mabs)
    (huniq : ∀ m' ∈ σ.messages.domain, m' ≠ mabs →
      recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) m' = false)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinvU : U.violated = .ok none)
    (hinvT : ∀ k, uint.nat m.index ≤ k → k < (toPState s).log.length →
      (truncSt U (idAbs m.dst) (idAbs m.src)
        (logAbs C C.length 1 ((toPState s).log.take k))).violated = .ok none)
    (hinvA : (truncSt U (idAbs m.dst) (idAbs m.src)
      (logAbs C C.length 1 es')).violated = .ok none)
    (hinvD : (doneSt (truncSt U (idAbs m.dst) (idAbs m.src)
      (logAbs C C.length 1 es')) mabs (uint.nat m.index) m.entries.length).violated = .ok none) :
    SimRun C (L ++ [e]) (doneSt (truncSt U (idAbs m.dst)
      (idAbs m.src) (logAbs C C.length 1 es')) mabs (uint.nat m.index) m.entries.length) := by
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
  have hpred : recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) mabs = true := by
    unfold recvPred
    have hn1 : (or ((msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)).ev.name == "ReceiveAppendEntriesRequest")
        ((msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)).ev.name == "ReceiveSnapshot")) = true := by
      simp [msgLine, evConv, hname']
    simp only [hn1, ↓reduceIte]
    rw [← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    have := isAER_app C C.length e m.dst s.vote xs m tm hmsg hm hty bmt bmc bi blt bk
    simp only [hmabs, Option.get_some] at this; exact this
  have hcontains : σ.server.contains (idAbs m.dst) = true := by
    rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  have hsm : (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)).stateMatches σ (idAbs m.dst) = true := by
    rw [← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    have := stateMatches_node C s (σ.s (idAbs m.dst)) e m.dst xs hR hs hpre hterm' hcommit' hrl
      hlog (hxs.trans hin) bt bc bl σ rfl hcontains
    unfold Etcdraft.Line.stateMatches at this ⊢
    simpa [msgLine, nodeLine] using this
  have hmt : mabs.type = .appendEntriesRequest := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmsub : mabs.subtype = "app" := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmterm : mabs.term = uint.Z m.term := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmprev : mabs.prevLogIndex = (uint.nat m.index : Nat) := by
    rw [hidxZ]; simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmpt : mabs.prevLogTerm = uint.Z m.logterm := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hments : mabs.entries = logAbs C C.length (uint.nat m.index + 1) m.entries := by
    simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmsrc : mabs.source = idAbs m.src := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmdst : mabs.dest = idAbs m.dst := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hUf := hFR.2.2
  apply simRun_snoc_chain C L σ _ e _ hrun hL hparse
  intro lines ts hl hts hl'
  have hlen := parseLines_length _ _ hl
  simp only [List.length_map] at hlen
  have hline := linesTrace_line_last C lines (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) ts.l (by omega)
  obtain ⟨tl, tsl, tpl⟩ := ts
  simp only at hts hl'
  subst hts hl'
  refine ⟨⟨doneSt (truncSt U (idAbs m.dst) (idAbs m.src)
    (logAbs C C.length 1 es')) mabs (uint.nat m.index) m.entries.length, L.length + 1 + 1, L.length + 1⟩, rfl, ?_⟩
  have hb : (linesTrace C (lines ++ [msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)])).bootstrap.getD
      (L.length + 1 - 1) false = false := by
    simp only [linesTrace]; simpa using hboot lines _ hl
  have hrecvN : Etcdraft.isReceiveName (((linesTrace C (lines ++ [msgLine e m.dst s.vote m.src m.dst
      (elements cfg.incoming)])).line (L.length + 1)).ev.name) = true := by
    rw [hline]; simp [msgLine, evConv, hname']; rfl
  have hone1 : Etcdraft.oneLessMessage tl U mabs = false := by
    unfold Etcdraft.oneLessMessage; rw [hUf.2.1]; simp; intro h; rw [h]; decide
  apply Chain.step _ _ ⟨U, L.length + 1, L.length + 1⟩ _ _ rfl
    (memEq_false_of_logs_or_term _ _ (idAbs m.dst) (by
      intro v hv; simp only [List.mem_singleton] at hv; subst hv
      exact ⟨List.contains_iff_mem.1 hcontains, Or.inr (fun h => hFR.2.1 h.symm)⟩)) hinvU
  · rw [← hmsrc, ← hmdst]
    rw [← hmsrc, ← hmdst] at hinvT hinvA hinvD
    rw [← hmdst] at hUf
    have := chain_appAccept (linesTrace C (lines ++ [msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)]))
      (L.length + 1) (L.length + 1) U mabs C C.length (uint.nat m.index)
      m.logterm lastnewi (toPState s).log m.entries es' [⟨tl, L.length + 1, tpl⟩]
      (by
        intro v hv; simp only [List.mem_singleton] at hv; subst hv
        refine ⟨by rw [hmdst]; exact List.contains_iff_mem.1 hcontains, ?_⟩
        simp only; rw [hmdst]; exact fun h => hFR.2.1 h.symm)
      (by simp) (by simp [linesTrace, Etcdraft.Trace.len]; omega) hb hrecvN
      (by rw [hUf.2.1]; exact hnd) (by rw [hUf.2.1]; exact hmem) (by rw [hUf.2.1]; exact hcnt)
      (by rw [hline]; exact hpred) (validatePre_later _ _ (by omega) _ _)
      (by rw [hUf.2.1, hline]; exact huniq)
      (by rw [hUf.1, hmdst]; exact hcontains) hmt hUf.2.2.1 (by rw [hUf.2.2.2.1]) hmsub
      (by rw [hUf.2.2.2.2.2, hmdst]; exact hR.2.2.2.2.2.1)
      hments hmprev hmpt (fun h => hlt0 h)
      (by rw [hUf.2.2.2.2.1, hmdst, hR.2.2.2.2.2.2.1, hidxZ]; omega) (fun k x hk hx => hs.2.2 k x (by omega) hx)
      hbe hwf (by word) hnw happ hinvT hinvA hinvD
    exact this
  · have := next_receive (linesTrace C (lines ++ [msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)]))
      ⟨tl, L.length + 1, tpl⟩ mabs _ (by simp)
      (by simp [linesTrace, Etcdraft.Trace.len]; omega) hb hrecvN hnd hmem
      (by rw [hline]; exact hpred)
      (by unfold Etcdraft.Trace.validatePreStates; rw [hline, hmdst, hsm]; simp)
      (fun m' hm' hne => by rw [hline]; simp [huniq m' hm' hne]) hFR.1
    rw [this]; simp [recvNext, hone1]

/-- **A two-round receive line, generically** (`simRun_recvMsg1`'s two-round counterpart): a first
round (`FirstRound`: `UpdateTerm`, or a candidate's `ReturnToFollower`) to `U`, then one handler
round `U.receive mabs = [S]` consuming the message. -/
theorem simRun_recvMsgU (C : List w64) (L : List TraceEv) (σ U S : Etcdraft.State) (hrun : SimRun C L σ)
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
    (hFR : FirstRound σ U mabs (idAbs m.dst))
    (hpred : recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) mabs = true)
    (hnd : σ.messages.domain.Nodup) (hmem : mabs ∈ σ.messages.domain)
    (hcnt : 0 < Etcdraft.Bag.count σ.messages mabs)
    (huniq : ∀ m' ∈ σ.messages.domain, m' ≠ mabs →
      recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) m' = false)
    (hrcv2 : U.receive mabs = .ok [S]) (hone2 : Etcdraft.oneLessMessage U S mabs = true)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinvU : U.violated = .ok none)
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
  have hUf := hFR.2.2
  apply simRun_recv2 C L σ _ S hrun hL e _ mabs hparse (by simp only [msgLine, evConv]; rw [hname']; exact hrecvnm)
    hnd hmem hcnt hpred _ huniq (by rw [hmdst]; exact List.contains_iff_mem.1 hcontains)
    hFR.1 hUf.2.1 hUf.1 (by rw [hmdst]; exact hFR.2.1)
    hrcv2 hone2 hboot hinvU hinv
  rw [hmdst, ← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
  have hsm := stateMatches_node C s (σ.s (idAbs m.dst)) e m.dst xs hR hs hpre hterm' hcommit' hrl
    hlog (hxs.trans hin) bt bc bl σ rfl hcontains
  unfold Etcdraft.Line.stateMatches at hsm ⊢
  simpa [msgLine, nodeLine] using hsm

/-- A specification role is never the pre-candidate's (raft's protocol reading has none). -/
theorem roleAbs_ne_pre (r : Role) : roleAbs r ≠ Etcdraft.preCandidate := by
  cases r <;> simp [roleAbs, Etcdraft.follower, Etcdraft.candidate, Etcdraft.leader, Etcdraft.preCandidate]

/-- The specification's handling of a response of the server's term (at a server that is not a
pre-candidate): a vote response's tally, an append response's match index (on success), the
message consumed. -/
def respSt (st : Etcdraft.State) (m : Etcdraft.Msg) : Etcdraft.State :=
  if m.type = .requestVoteResponse then voteRespResult st m.dest m.source m
  else if m.success then (withMatch st m.dest m.source m.matchIndex).discard m else st.discard m

/-- **A response of the server's term** (`HandleRequestVoteResponse`, `HandleAppendEntriesResponse`;
one round, whatever the server's role but pre-candidate). -/
theorem receive_resp (st : Etcdraft.State) (m : Etcdraft.Msg) (hsrv : st.server.contains m.dest = true)
    (hty : m.type = .requestVoteResponse ∨ m.type = .appendEntriesResponse)
    (hterm : m.term = (st.s m.dest).currentTerm) (hnp : (st.s m.dest).state ≠ Etcdraft.preCandidate) :
    st.receive m = .ok [respSt st m] := by
  unfold Etcdraft.State.receive
  have hut : st.updateTerm m.dest m.source m = none := by
    unfold Etcdraft.State.updateTerm; simp [hterm]
  have hds : st.dropStaleResponse m.dest m.source m = none := by
    unfold Etcdraft.State.dropStaleResponse; simp [hterm]
  have hsrv' : m.dest ∈ st.server := List.contains_iff_mem.1 hsrv
  rcases hty with hty | hty
  · have hh : st.handleRequestVoteResponse m.dest m.source m = some (respSt st m) := by
      unfold Etcdraft.State.handleRequestVoteResponse respSt voteRespResult
      simp [hterm, hnp, hty]
    simp [hsrv', hty, hut, hds, hh, Etcdraft.somes, pure, Except.pure]
  · have hh : st.handleAppendEntriesResponse m.dest m.source m = some (respSt st m) := by
      unfold Etcdraft.State.handleAppendEntriesResponse respSt withMatch
      cases m.success <;> simp [hterm, hty]
    simp [hsrv', hty, hut, hds, hh, Etcdraft.somes, pure, Except.pure]

theorem oneLess_resp (st : Etcdraft.State) (m : Etcdraft.Msg) (hnd : st.messages.domain.Nodup)
    (hm : 0 < Etcdraft.Bag.count st.messages m) : Etcdraft.oneLessMessage st (respSt st m) m = true := by
  unfold respSt
  split
  · exact oneLess_voteResp st _ _ m hnd hm
  · split
    · exact oneLess_discard st _ m rfl hnd hm
    · exact oneLess_discard st _ m rfl hnd hm

/-- The response's line: its name and the line matching the response. -/
theorem respLine (C : List w64) (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg) (evt : w64)
    (htyev : (m.ty = .appResp ∧ evt = W64 12) ∨ (m.ty = .voteResp ∧ evt = W64 16))
    (hname : evtNames[uint.nat evt]? = some e.name) (tm : TraceMsg) (hmsg : e.msg = some tm)
    (hm : MsgEvOf m tm) (bmt : uint.Z m.term < 2 ^ 63) (bi : uint.Z m.index < 2 ^ 63)
    (mabs : Etcdraft.Msg) (hmabs : msgAbs C C.length m = some mabs) :
    ∃ nm, gsStr e.name = nm ∧ Etcdraft.isReceiveName nm = true ∧
      (Etcdraft.raftMsgType (gsStr (msgTypeStr m.ty))).isSome = true ∧
      (mabs.type = .requestVoteResponse ∨ mabs.type = .appendEntriesResponse) ∧
      mabs.dest = idAbs m.dst ∧ mabs.term = uint.Z m.term ∧
      recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) mabs = true := by
  have hnames := recvName_of evt e hname
  rcases htyev with ⟨hty, rfl⟩ | ⟨hty, rfl⟩
  · have hname' := hnames.2.1 rfl
    refine ⟨_, hname', by rfl, by rw [hty]; rfl, ?_, ?_, ?_, ?_⟩
    · right; simp [msgAbs, hty] at hmabs; rw [← hmabs]
    · simp [msgAbs, hty] at hmabs; rw [← hmabs]
    · simp [msgAbs, hty] at hmabs; rw [← hmabs]
    · rw [recvPred_aeresp _ _ (by rw [msgLine_name, hname'])]
      have := isAEResp_any C C.length e m.dst s.vote (elements cfg.incoming) m tm hmsg hm hty bmt bi
      simp only [hmabs, Option.get_some] at this; exact this
  · have hname' := hnames.2.2.2 rfl
    refine ⟨_, hname', by rfl, by rw [hty]; rfl, ?_, ?_, ?_, ?_⟩
    · left; simp [msgAbs, hty] at hmabs; rw [← hmabs]
    · simp [msgAbs, hty] at hmabs; rw [← hmabs]
    · simp [msgAbs, hty] at hmabs; rw [← hmabs]
    · rw [recvPred_rvresp _ _ (by rw [msgLine_name, hname'])]
      have := isRVResp_voteResp C C.length e m.dst s.vote (elements cfg.incoming) m tm hmsg hm hty bmt
      simp only [hmabs, Option.get_some] at this; exact this

/-- **A response of the node's term's receive line's step** (any role: a candidate's tally, a
leader's match, a follower's or a stale role's recorded and ignored response). -/
theorem simRun_recvResp (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg) (evt : w64)
    (htyev : (m.ty = .appResp ∧ evt = W64 12) ∨ (m.ty = .voteResp ∧ evt = W64 16))
    (hev : SendEvOf evt m.dst s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : m.dst ∈ C) (hsrv : σ.server = confAbs C)
    (hR : SimServerR C C.length (toPState s) (σ.s (idAbs m.dst))) (hs : LogShapeOk C.length (toPState s))
    (hpre : s.role ≠ .preCandidate) (hterm : m.term = s.term)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (bi : uint.Z m.index < 2 ^ 63)
    (mabs : Etcdraft.Msg) (hmabs : msgAbs C C.length m = some mabs)
    (hnd : σ.messages.domain.Nodup) (hmem : mabs ∈ σ.messages.domain)
    (hcnt : 0 < Etcdraft.Bag.count σ.messages mabs)
    (huniq : ∀ m' ∈ σ.messages.domain, m' ≠ mabs →
      recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) m' = false)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinv : (respSt σ mabs).violated = .ok none) :
    SimRun C (L ++ [e]) (respSt σ mabs) := by
  have hev' := hev
  obtain ⟨hname, -, -, -, -, -, -, -, ⟨tm, hmsg, hm⟩, -⟩ := hev'
  obtain ⟨nm, hname', hrn, htyp, hmt, hmdst, hmterm, hpred⟩ :=
    respLine C e s cfg m evt htyev hname tm hmsg hm (by rw [hterm]; exact bt) bi mabs hmabs
  have hcontains : σ.server.contains (idAbs m.dst) = true := by
    rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  have hnp : (σ.s mabs.dest).state ≠ Etcdraft.preCandidate := by rw [hmdst, hR.2.1]; exact roleAbs_ne_pre _
  exact simRun_recvMsg1 C L σ _ hrun hL e s cfg m evt nm hev hname' hrn htyp hin hout hC hsrv hR hs hpre bt bc bl
    mabs hmdst hpred hnd hmem hcnt huniq
    (receive_resp σ mabs (by rw [hmdst]; exact hcontains) hmt (by rw [hmdst, hR.1, hmterm, hterm]; rfl) hnp)
    (by unfold respSt; split; · rfl
        split <;> rfl) hboot hinv

/-- **A higher-term response's receive line's step**: `UpdateTerm`, then the response at the new
term (recorded at the new follower). -/
theorem simRun_recvRespHigher (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg) (evt : w64)
    (htyev : (m.ty = .appResp ∧ evt = W64 12) ∨ (m.ty = .voteResp ∧ evt = W64 16))
    (hev : SendEvOf evt m.dst s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : m.dst ∈ C) (hsrv : σ.server = confAbs C)
    (hR : SimServerR C C.length (toPState s) (σ.s (idAbs m.dst))) (hs : LogShapeOk C.length (toPState s))
    (hpre : s.role ≠ .preCandidate) (hgt : uint.Z s.term < uint.Z m.term)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (bi : uint.Z m.index < 2 ^ 63)
    (bmt : uint.Z m.term < 2 ^ 63)
    (mabs : Etcdraft.Msg) (hmabs : msgAbs C C.length m = some mabs)
    (hnd : σ.messages.domain.Nodup) (hmem : mabs ∈ σ.messages.domain)
    (hcnt : 0 < Etcdraft.Bag.count σ.messages mabs)
    (huniq : ∀ m' ∈ σ.messages.domain, m' ≠ mabs →
      recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) m' = false)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinvU : (σ.becomeFollowerOfTerm (idAbs m.dst) mabs.term).violated = .ok none)
    (hinv : (respSt (σ.becomeFollowerOfTerm (idAbs m.dst) mabs.term) mabs).violated = .ok none) :
    SimRun C (L ++ [e]) (respSt (σ.becomeFollowerOfTerm (idAbs m.dst) mabs.term) mabs) := by
  have hev' := hev
  obtain ⟨hname, -, -, -, -, -, -, -, ⟨tm, hmsg, hm⟩, -⟩ := hev'
  obtain ⟨nm, hname', hrn, htyp, hmt, hmdst, hmterm, hpred⟩ :=
    respLine C e s cfg m evt htyev hname tm hmsg hm bmt bi mabs hmabs
  have hcontains : σ.server.contains (idAbs m.dst) = true := by
    rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  have hFR := firstRound_updateTerm σ mabs (idAbs m.dst) hmdst hcontains (by rcases hmt with h | h <;> simp [h])
    (by rw [hR.1, hmterm]; exact hgt)
  have hUf := hFR.2.2
  exact simRun_recvMsgU C L σ _ _ hrun hL e s cfg m evt nm hev hname' hrn htyp hin hout hC hsrv hR hs hpre bt bc bl
    mabs hmdst hFR hpred hnd hmem hcnt huniq
    (receive_resp _ mabs (by rw [hmdst, hUf.1]; exact hcontains) hmt (by rw [hmdst, hUf.2.2.2.1])
      (by rw [hmdst, hUf.2.2.1]; decide))
    (oneLess_resp _ mabs (by rw [hUf.2.1]; exact hnd) (by rw [hUf.2.1]; exact hcnt)) hboot hinvU hinv

/-- The append request line's predicate and name facts, for `simRun_recvMsg2`. -/
theorem aerLine (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg)
    (hname : evtNames[uint.nat (W64 10)]? = some e.name) :
    gsStr e.name = "ReceiveAppendEntriesRequest" ∧ Etcdraft.isReceiveName "ReceiveAppendEntriesRequest" = true ∧
    ∀ mabs, recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) mabs =
      (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)).isAppendEntriesRequest mabs := by
  have hname' : gsStr e.name = "ReceiveAppendEntriesRequest" := by
    simp only [evtNames] at hname
    have : e.name = go!"ReceiveAppendEntriesRequest" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  exact ⟨hname', by rfl, fun mabs => recvPred_aer _ _ (by rw [msgLine_name, hname'])⟩

/-- **A higher-term heartbeat's receive line's step**: `UpdateTerm`, then the heartbeat at the new
follower. -/
theorem simRun_recvHeartbeatU (C : List w64) (L : List TraceEv) (σ U : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg) (hty : m.ty = .heartbeat)
    (hev : SendEvOf (W64 10) m.dst s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : m.dst ∈ C) (hsrv : σ.server = confAbs C)
    (hR : SimServerR C C.length (toPState s) (σ.s (idAbs m.dst))) (hs : LogShapeOk C.length (toPState s))
    (hpre : s.role ≠ .preCandidate) (hents : m.entries = [])
    (hc1 : 1 ≤ uint.Z (toPState s).commit)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (bmc : uint.Z m.commit < 2 ^ 63) (bmt : uint.Z m.term < 2 ^ 63)
    (mabs : Etcdraft.Msg) (hmabs : msgAbs C C.length m = some mabs)
    (hFR : FirstRound σ U mabs (idAbs m.dst))
    (hnd : σ.messages.domain.Nodup) (hmem : mabs ∈ σ.messages.domain)
    (hcnt : 0 < Etcdraft.Bag.count σ.messages mabs)
    (huniq : ∀ m' ∈ σ.messages.domain, m' ≠ mabs →
      recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) m' = false)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinvU : U.violated = .ok none)
    (hinv : (hbRecvSt U mabs).violated = .ok none) :
    SimRun C (L ++ [e]) (hbRecvSt U mabs) := by
  have hev' := hev
  obtain ⟨hname, -, -, -, -, -, -, ⟨xs, ys, hxs, hys, -⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev'
  obtain ⟨hname', hrn, hrp⟩ := aerLine e s cfg m hname
  have hmt : mabs.type = .appendEntriesRequest := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmsub : mabs.subtype = "heartbeat" := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmterm : mabs.term = uint.Z m.term := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmprev : mabs.prevLogIndex = 0 := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hments : mabs.entries = [] := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmdst : mabs.dest = idAbs m.dst := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hcontains : σ.server.contains (idAbs m.dst) = true := by
    rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  have hUf := hFR.2.2
  have hpred : recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) mabs = true := by
    rw [hrp, ← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    have := isAER_heartbeat C C.length e m.dst s.vote xs m tm hmsg hm hty hents bmt bmc
    simp only [hmabs, Option.get_some] at this; exact this
  refine simRun_recvMsgU C L σ U _ hrun hL e s cfg m _ _ hev hname' hrn (by rw [hty]; rfl) hin hout hC hsrv hR hs
    hpre bt bc bl mabs hmdst hFR hpred hnd hmem hcnt huniq
    ?_ (oneLess_of_msgs _ _ mabs (by rfl) (by rw [hUf.2.1]; exact hnd) (by rw [hUf.2.1]; exact hcnt)) hboot hinvU hinv
  have := receive_heartbeat U mabs
    (by rw [hmdst, hUf.1]; exact hcontains) hmt (by rw [hmdst, hUf.2.2.1]) (by rw [hmdst, hUf.2.2.2.1]) hmsub hmprev
    hments (by rw [hmdst, hUf.2.2.2.2.1, hR.2.2.2.2.2.2.1]; exact hc1)
  rw [this]; rfl

/-- **A higher-term stale append request's receive line's step**: `UpdateTerm`, then the request
answered with the commit index at the new follower (raft's `appStale` after `becomeFollower`). -/
theorem simRun_recvStaleU (C : List w64) (L : List TraceEv) (σ U : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg) (hty : m.ty = .app)
    (hev : SendEvOf (W64 10) m.dst s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : m.dst ∈ C) (hsrv : σ.server = confAbs C)
    (hR : SimServerR C C.length (toPState s) (σ.s (idAbs m.dst))) (hs : LogShapeOk C.length (toPState s))
    (hpre : s.role ≠ .preCandidate)
    (hst : uint.Z m.index < uint.Z (toPState s).commit)
    (hmt0 : PlogMatches (entryID.mk (W64 0) (W64 0)) (toPState s).log (entryID.mk m.logterm (W64 (uint.nat m.index))))
    (hlt0 : uint.nat m.index = 0 → m.logterm = W64 0)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (bmc : uint.Z m.commit < 2 ^ 63)
    (bi : uint.Z m.index < 2 ^ 63) (blt : uint.Z m.logterm < 2 ^ 63) (bk : m.entries.length < 2 ^ 63)
    (bmt : uint.Z m.term < 2 ^ 63)
    (mabs : Etcdraft.Msg) (hmabs : msgAbs C C.length m = some mabs)
    (hFR : FirstRound σ U mabs (idAbs m.dst))
    (hnd : σ.messages.domain.Nodup) (hmem : mabs ∈ σ.messages.domain)
    (hcnt : 0 < Etcdraft.Bag.count σ.messages mabs)
    (huniq : ∀ m' ∈ σ.messages.domain, m' ≠ mabs →
      recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) m' = false)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinvU : U.violated = .ok none)
    (hinv : (staleRecvSt U mabs).violated = .ok none) :
    SimRun C (L ++ [e]) (staleRecvSt U mabs) := by
  have hev' := hev
  obtain ⟨hname, -, -, -, -, -, -, ⟨xs, ys, hxs, hys, -⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev'
  obtain ⟨hname', hrn, hrp⟩ := aerLine e s cfg m hname
  have hmt : mabs.type = .appendEntriesRequest := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmsub : mabs.subtype = "app" := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmterm : mabs.term = uint.Z m.term := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hidxZ : ((uint.nat m.index : Nat) : Int) = uint.Z m.index := by word
  have hmprev : mabs.prevLogIndex = (uint.nat m.index : Nat) := by
    rw [hidxZ]; simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmpt : mabs.prevLogTerm = uint.Z m.logterm := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmdst : mabs.dest = idAbs m.dst := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hcontains : σ.server.contains (idAbs m.dst) = true := by
    rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  have hUf := hFR.2.2
  have hpred : recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) mabs = true := by
    rw [hrp, ← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    have := isAER_app C C.length e m.dst s.vote xs m tm hmsg hm hty bmt bmc bi blt bk
    simp only [hmabs, Option.get_some] at this; exact this
  refine simRun_recvMsgU C L σ U _ hrun hL e s cfg m _ _ hev hname' hrn (by rw [hty]; rfl) hin hout hC hsrv hR hs
    hpre bt bc bl mabs hmdst hFR hpred hnd hmem hcnt huniq
    ?_ (oneLess_of_msgs _ _ mabs (by rfl) (by rw [hUf.2.1]; exact hnd) (by rw [hUf.2.1]; exact hcnt)) hboot hinvU hinv
  have hlok : LogOkL mabs (U.s mabs.dest).log = true := by
    rw [hmdst, hUf.2.2.2.2.2, hR.2.2.2.2.2.1, logOkL_abs C C.length mabs _ (uint.nat m.index) m.logterm hmprev hmpt
      (fun k x hk hx => hs.2.2 k x (by omega) hx) hlt0 (by word), decide_eq_true_iff]
    exact hmt0
  have := receive_appStale U mabs
    (by rw [hmdst, hUf.1]; exact hcontains) hmt (by rw [hmdst, hUf.2.2.1]) (by rw [hmdst, hUf.2.2.2.1]) hmsub
    (by rw [hmdst, hUf.2.2.2.2.1, hR.2.2.2.2.2.2.1, hmprev, hidxZ]; omega) hlok
  rw [this]; rfl

/-- **A higher-term rejected append request's receive line's step**: `UpdateTerm`, then the
rejection at the new follower (pre-vote and check-quorum off). -/
theorem simRun_recvRejectU (C : List w64) (L : List TraceEv) (σ U : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg) (hty : m.ty = .app)
    (hev : SendEvOf (W64 10) m.dst s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : m.dst ∈ C) (hsrv : σ.server = confAbs C) (hpv : U.preVote = false) (hcq : U.checkQuorum = false)
    (hR : SimServerR C C.length (toPState s) (σ.s (idAbs m.dst))) (hs : LogShapeOk C.length (toPState s))
    (hpre : s.role ≠ .preCandidate)
    (hmt0 : ¬ PlogMatches (entryID.mk (W64 0) (W64 0)) (toPState s).log (entryID.mk m.logterm (W64 (uint.nat m.index))))
    (hlt0 : uint.nat m.index = 0 → m.logterm = W64 0)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (bmc : uint.Z m.commit < 2 ^ 63)
    (bi : uint.Z m.index < 2 ^ 63) (blt : uint.Z m.logterm < 2 ^ 63) (bk : m.entries.length < 2 ^ 63)
    (bmt : uint.Z m.term < 2 ^ 63)
    (mabs : Etcdraft.Msg) (hmabs : msgAbs C C.length m = some mabs)
    (hFR : FirstRound σ U mabs (idAbs m.dst))
    (hnd : σ.messages.domain.Nodup) (hmem : mabs ∈ σ.messages.domain)
    (hcnt : 0 < Etcdraft.Bag.count σ.messages mabs)
    (huniq : ∀ m' ∈ σ.messages.domain, m' ≠ mabs →
      recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) m' = false)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinvU : U.violated = .ok none)
    (hinv : (rejRecvSt U mabs).violated = .ok none) :
    SimRun C (L ++ [e]) (rejRecvSt U mabs) := by
  have hev' := hev
  obtain ⟨hname, -, -, -, -, -, -, ⟨xs, ys, hxs, hys, -⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev'
  obtain ⟨hname', hrn, hrp⟩ := aerLine e s cfg m hname
  have hmt : mabs.type = .appendEntriesRequest := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmterm : mabs.term = uint.Z m.term := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hidxZ : ((uint.nat m.index : Nat) : Int) = uint.Z m.index := by word
  have hmprev : mabs.prevLogIndex = (uint.nat m.index : Nat) := by
    rw [hidxZ]; simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmpt : mabs.prevLogTerm = uint.Z m.logterm := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmdst : mabs.dest = idAbs m.dst := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hcontains : σ.server.contains (idAbs m.dst) = true := by
    rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  have hUf := hFR.2.2
  have hpred : recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) mabs = true := by
    rw [hrp, ← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    have := isAER_app C C.length e m.dst s.vote xs m tm hmsg hm hty bmt bmc bi blt bk
    simp only [hmabs, Option.get_some] at this; exact this
  refine simRun_recvMsgU C L σ U _ hrun hL e s cfg m _ _ hev hname' hrn (by rw [hty]; rfl) hin hout hC hsrv hR hs
    hpre bt bc bl mabs hmdst hFR hpred hnd hmem hcnt huniq
    ?_ (oneLess_of_msgs _ _ mabs (by rfl) (by rw [hUf.2.1]; exact hnd) (by rw [hUf.2.1]; exact hcnt)) hboot hinvU hinv
  have hlok : LogOkL mabs (U.s mabs.dest).log = false := by
    rw [hmdst, hUf.2.2.2.2.2, hR.2.2.2.2.2.1, logOkL_abs C C.length mabs _ (uint.nat m.index) m.logterm hmprev hmpt
      (fun k x hk hx => hs.2.2 k x (by omega) hx) hlt0 (by word)]
    exact decide_eq_false hmt0
  have := receive_appReject U mabs
    (by rw [hmdst, hUf.1]; exact hcontains) hmt (by rw [hmdst, hUf.2.2.1]) (by rw [hmdst, hUf.2.2.2.1])
    hpv hcq hlok
  rw [this]; rfl

/-! ### `BecomeFollower` lines -/

/-- A skipped `BecomeFollower` line's non-receive successor: the state itself. -/
theorem nonReceive_bfSkip (t : Etcdraft.Trace) (ts : Etcdraft.TState)
    (hname : (t.line ts.l).ev.name = "BecomeFollower")
    (hskip : t.isBecomeFollowerInUpdateTermOrReturnToFollower ts = true) :
    t.nonReceive ts = .ok [ts.s] := by
  have hf : t.server.flatMap (t.stepDownToFollowerIfLogged ts) = [] := by
    rw [List.flatMap_eq_nil_iff]; intro i _
    simp [Etcdraft.Trace.stepDownToFollowerIfLogged, hskip]
  unfold Etcdraft.Trace.nonReceive
  simp only [hname, hf]
  simp [Etcdraft.Trace.skipUnusedLogline, hskip, pure, Except.pure, bind, Except.bind]

theorem parseLine_ev (k : Nat) (ev : Etcdraft.Event) (ln : Etcdraft.Line) (h : Etcdraft.parseLine k ev = .ok ln) :
    ln.ev = ev := by
  unfold Etcdraft.parseLine at h
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
  repeat' (first | (split at h) | (cases h; rfl) | (cases h))


theorem mapM_ok_map {α β γ ε : Type} (f : α → Except ε β) (g : β → γ) (h : α → γ)
    (hfg : ∀ a b, f a = .ok b → g b = h a) :
    ∀ (l : List α) (r : List β), l.mapM f = .ok r → r.map g = l.map h := by
  intro l
  induction l with
  | nil => intro r hr; simp [List.mapM_nil, pure, Except.pure] at hr; subst hr; rfl
  | cons a l ih =>
    intro r hr
    rw [List.mapM_cons] at hr
    simp only [bind, Except.bind] at hr
    cases hf : f a with
    | error e => rw [hf] at hr; cases hr
    | ok b =>
      rw [hf] at hr
      simp only at hr
      cases hm : l.mapM f with
      | error e => rw [hm] at hr; cases hr
      | ok r' =>
        rw [hm] at hr
        simp only [pure, Except.pure, Except.ok.injEq] at hr
        subst hr
        simp [hfg a b hf, ih r' hm]

/-- The parsed lines' events are the events. -/
theorem parseLines_ev (evs : List Etcdraft.Event) (lines : List Etcdraft.Line) (h : parseLines evs = .ok lines) :
    lines.map Etcdraft.Line.ev = evs := by
  unfold parseLines at h
  have := mapM_ok_map _ Etcdraft.Line.ev Prod.snd (fun p ln hp => parseLine_ev p.1 p.2 ln hp) _ _ h
  rw [this]
  apply List.ext_getElem (by simp)
  intro n h1 h2; simp

/-- `SelectLastInSubSeq`'s fold: the last index (from 1) where `f` holds. -/
theorem foldl_last (f : Nat → Bool) (j : Nat) (hj : f j = true) :
    ∀ N, j < N → (∀ n, j < n → n < N → f n = false) →
      (List.range N).foldl (fun (acc : Nat) n => if f n then n + 1 else acc) 0 = j + 1 := by
  intro N
  induction N with
  | zero => intro h; omega
  | succ N ih =>
    intro hjN hrest
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rcases Nat.lt_or_ge j N with hlt | hge
    · rw [ih hlt (fun n h1 h2 => hrest n h1 (by omega)), hrest N hlt (by omega)]; rfl
    · have : j = N := by omega
      subst this; simp [hj]

/-- **Which `BecomeFollower` line is skipped**: the test on the node's last line (`e0`, the lines
after it of other nodes). -/
theorem isBF_eq (C : List w64) (L : List TraceEv) (lines : List Etcdraft.Line) (e : TraceEv) (id vote : w64)
    (xs : List w64) (ts : Etcdraft.TState) (hl : parseLines (L.map evConv) = .ok lines) (hl' : ts.l = L.length + 1)
    (hname' : gsStr e.name = "BecomeFollower")
    (L1 L2 : List TraceEv) (e0 : TraceEv) (hsplit : L = L1 ++ e0 :: L2)
    (hnid0 : (evConv e0).nid = (evConv e).nid) (hnid2 : ∀ x ∈ L2, (evConv x).nid ≠ (evConv e).nid) :
    (linesTrace C (lines ++ [nodeLine e id vote xs])).isBecomeFollowerInUpdateTermOrReturnToFollower ts =
      bfCond (evConv e0) (evConv e) := by
  have hlen := parseLines_length _ _ hl
  simp only [List.length_map] at hlen
  have hev := parseLines_ev _ _ hl
  have hline := linesTrace_line_last C lines (nodeLine e id vote xs) ts.l (by omega)
  have hlineN : ∀ n (hn : n < L.length),
      ((linesTrace C (lines ++ [nodeLine e id vote xs])).line (n + 1)).ev = evConv L[n] := by
    intro n hn
    simp only [linesTrace, Etcdraft.Trace.line, List.getD_eq_getElem?_getD, Nat.add_sub_cancel]
    rw [List.getElem?_append_left (by omega)]
    have := congrArg (fun l => l[n]?) hev
    simp only [List.getElem?_map] at this
    rw [List.getElem?_eq_getElem (by omega)] at this ⊢
    rw [List.getElem?_eq_getElem hn] at this
    simp only [Option.map_some, Option.getD_some, Option.some.injEq] at this ⊢
    exact this
  have hL1 : L1.length < L.length := by rw [hsplit]; simp
  have he0 : L[L1.length] = e0 := by simp [hsplit]
  unfold Etcdraft.Trace.isBecomeFollowerInUpdateTermOrReturnToFollower
  have hev1 : Etcdraft.Trace.isEvent (linesTrace C (lines ++ [nodeLine e id vote xs])) ts "BecomeFollower" = true := by
    unfold Etcdraft.Trace.isEvent; rw [hline]
    simp [nodeLine, evConv, hname', linesTrace, Etcdraft.Trace.len, hl', hlen]
  simp only [hev1, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hk : (List.range (ts.l - 1)).foldl (fun (acc : Nat) n =>
      if ((linesTrace C (lines ++ [nodeLine e id vote xs])).line (n + 1)).ev.nid ==
        ((linesTrace C (lines ++ [nodeLine e id vote xs])).line ts.l).ev.nid then n + 1 else acc) 0 =
      L1.length + 1 := by
    apply foldl_last _ L1.length _ _ (by omega)
    · intro n h1 h2
      have hn : n < L.length := by omega
      rw [hlineN n hn, hline]
      have hx : L[n] ∈ L2 := by
        have h3 : n - L1.length - 1 < L2.length := by
          have := hn; rw [hsplit] at this; simp at this; omega
        have : L[n] = L2[n - L1.length - 1] := by
          simp only [hsplit]; rw [List.getElem_append_right (by omega)]
          rw [List.getElem_cons (by simp; omega)]
          simp [show n - L1.length ≠ 0 by omega]
        rw [this]; exact List.getElem_mem h3
      simp only [nodeLine]
      simpa using hnid2 _ hx
    · rw [hlineN _ hL1, hline, he0]; simp only [nodeLine]; simpa using hnid0
  rw [hk]
  simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, beq_iff_eq, ↓reduceIte]
  rw [hlineN _ hL1, he0, hline]
  unfold bfCond
  cases (evConv e0).msg <;> simp [nodeLine]

/-- **A skipped `BecomeFollower` line's step** (raft's `becomeFollower` inside a receipt's handling:
`UpdateTerm` or `ReturnToFollower`, done at the receive line): the node's last line before it is that
receive line (`e0`, of a higher-term message, or a candidate's append request of its term), the state
unchanged. -/
theorem simRun_bfSkip (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (id : w64) (s : NState) (cfg : CfgM)
    (hev : NodeEvOf (W64 2) id s cfg e) (hout : cfg.outgoing = ∅)
    (L1 L2 : List TraceEv) (e0 : TraceEv) (hsplit : L = L1 ++ e0 :: L2)
    (hnid0 : (evConv e0).nid = (evConv e).nid) (hnid2 : ∀ x ∈ L2, (evConv x).nid ≠ (evConv e).nid)
    (hcond : bfCond (evConv e0) (evConv e) = true)
    (hboot : ∀ lines (ln : Etcdraft.Line), parseLines (L.map evConv) = .ok lines → ln.nid = idAbs id →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinv : σ.violated = .ok none) :
    SimRun C (L ++ [e]) σ := by
  obtain ⟨hname, hnid, -, hvote, -, -, -, ⟨xs, ys, -, hys, hconf⟩, hmsg, -, -, -, -⟩ := hev
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  have hname' : gsStr e.name = "BecomeFollower" := by
    simp only [evtNames] at hname
    have : e.name = go!"BecomeFollower" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  apply simRun_node C L σ _ hrun hL e id s.vote xs hnid hvote hconf hmsg (by rw [hname']; rfl)
    (by rw [hname']; rfl) (by rw [hname']; decide) (fun lines hl => hboot lines _ hl rfl) _ hinv
  intro lines ts hl hts hl'
  have hlen := parseLines_length _ _ hl
  simp only [List.length_map] at hlen
  have hline := linesTrace_line_last C lines (nodeLine e id s.vote xs) ts.l (by omega)
  rw [← hts]
  apply nonReceive_bfSkip _ ts (by rw [hline]; simp [nodeLine, evConv, hname'])
  rw [isBF_eq C L lines e id s.vote xs ts hl hl' hname' L1 L2 e0 hsplit hnid0 hnid2, hcond]

/-- A step-down `BecomeFollower` line's non-receive successor: `StepDownToFollower` at its node. -/
theorem nonReceive_stepDown (t : Etcdraft.Trace) (ts : Etcdraft.TState) (i : Etcdraft.ID) (hl : ts.l ≤ t.len)
    (hname : (t.line ts.l).ev.name = "BecomeFollower") (hnid : (t.line ts.l).nid = i)
    (hnd : t.server.Nodup) (hi : i ∈ t.server)
    (hskip : t.isBecomeFollowerInUpdateTermOrReturnToFollower ts = false)
    (hst : (ts.s.s i).state = Etcdraft.leader ∨ (ts.s.s i).state = Etcdraft.candidate)
    (hpost : (t.line ts.l).stateMatches (ts.s.becomeFollowerOfTerm i (ts.s.s i).currentTerm) i = true) :
    t.nonReceive ts = .ok [ts.s.becomeFollowerOfTerm i (ts.s.s i).currentTerm] := by
  have hsd : ts.s.stepDownToFollower i = some (ts.s.becomeFollowerOfTerm i (ts.s.s i).currentTerm) := by
    unfold Etcdraft.State.stepDownToFollower
    rcases hst with h | h <;> simp [h]
  have hf : t.server.flatMap (t.stepDownToFollowerIfLogged ts) =
      [ts.s.becomeFollowerOfTerm i (ts.s.s i).currentTerm] := by
    apply flatMap_single _ _ i _ hnd hi
    · simp [Etcdraft.Trace.stepDownToFollowerIfLogged, Etcdraft.Trace.isNodeEvent, Etcdraft.Trace.isEvent,
        hl, hname, hnid, hskip, hsd, Etcdraft.Trace.validatePostStates, hpost]
    · intro j _ hj
      simp [Etcdraft.Trace.stepDownToFollowerIfLogged, Etcdraft.Trace.isNodeEvent, Etcdraft.Trace.isEvent,
        hnid, Ne.symm hj]
  unfold Etcdraft.Trace.nonReceive
  simp only [hname, hf]
  simp [Etcdraft.Trace.skipUnusedLogline, Etcdraft.Trace.isEvent, hname, hskip, pure, Except.pure, bind,
    Except.bind]

/-- **A step-down `BecomeFollower` line's step** (raft's `becomeFollower(r.Term, None)` outside a
receipt's first round: a candidate losing its election): `StepDownToFollower`, the line's state
(raft's after it, `s`) related to the server stepped down. -/
theorem simRun_bfStepDown (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hrun : SimRun C L σ)
    (hL : L ≠ []) (e : TraceEv) (id : w64) (s : NState) (cfg : CfgM)
    (hev : NodeEvOf (W64 2) id s cfg e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : id ∈ C) (hsrv : σ.server = confAbs C)
    (L1 L2 : List TraceEv) (e0 : TraceEv) (hsplit : L = L1 ++ e0 :: L2)
    (hnid0 : (evConv e0).nid = (evConv e).nid) (hnid2 : ∀ x ∈ L2, (evConv x).nid ≠ (evConv e).nid)
    (hcond : bfCond (evConv e0) (evConv e) = false)
    (hst : (σ.s (idAbs id)).state = Etcdraft.leader ∨ (σ.s (idAbs id)).state = Etcdraft.candidate)
    (hR : SimServerR C C.length (toPState s)
      ((σ.becomeFollowerOfTerm (idAbs id) (σ.s (idAbs id)).currentTerm).s (idAbs id)))
    (hs : LogShapeOk C.length (toPState s)) (hpre : s.role ≠ .preCandidate)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63)
    (hboot : ∀ lines (ln : Etcdraft.Line), parseLines (L.map evConv) = .ok lines → ln.nid = idAbs id →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hinv : (σ.becomeFollowerOfTerm (idAbs id) (σ.s (idAbs id)).currentTerm).violated = .ok none) :
    SimRun C (L ++ [e]) (σ.becomeFollowerOfTerm (idAbs id) (σ.s (idAbs id)).currentTerm) := by
  obtain ⟨hname, hnid, hterm', hvote, hcommit', hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, hmsg, -, -, -, -⟩ := hev
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  have hname' : gsStr e.name = "BecomeFollower" := by
    simp only [evtNames] at hname
    have : e.name = go!"BecomeFollower" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  have hcontains : σ.server.contains (idAbs id) = true := by
    rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  apply simRun_node C L σ _ hrun hL e id s.vote xs hnid hvote hconf hmsg (by rw [hname']; rfl)
    (by rw [hname']; rfl) (by rw [hname']; decide) (fun lines hl => hboot lines _ hl rfl) _ hinv
  intro lines ts hl hts hl'
  have hlen := parseLines_length _ _ hl
  simp only [List.length_map] at hlen
  have hline := linesTrace_line_last C lines (nodeLine e id s.vote xs) ts.l (by omega)
  subst hts
  apply nonReceive_stepDown _ ts (idAbs id) (by simp [linesTrace, Etcdraft.Trace.len]; omega)
    (by rw [hline]; simp [nodeLine, evConv, hname']) (by rw [hline]; rfl) (confAbs_nodup C)
    (by simp only [linesTrace]; rw [mem_confAbs]; exact hC)
    (by rw [isBF_eq C L lines e id s.vote xs ts hl hl' hname' L1 L2 e0 hsplit hnid0 hnid2, hcond]) hst
  rw [hline]
  exact stateMatches_node C s _ e id xs hR hs hpre hterm' hcommit' hrl hlog (hxs.trans hin) bt bc bl _ rfl
    (by simp [Etcdraft.State.becomeFollowerOfTerm, Etcdraft.State.upd]; exact List.contains_iff_mem.1 hcontains)

/-! ### Line effects (testing `LineEffect`, the Draft's) -/

theorem withNode_same (σ : Etcdraft.State) (i : Etcdraft.ID) (fP : Etcdraft.Bag → Etcdraft.Bag) :
    withNode σ i (σ.s i) id fP = { σ with pendingMessages := fP σ.pendingMessages } := by
  unfold withNode
  have : (fun j => if j = i then σ.s i else σ.s j) = σ.s := by funext j; split <;> simp_all
  rw [this]; rfl

/-- **A heartbeat send's effect**: the leader's server unchanged, the heartbeat pending. -/
theorem lineEffect_heartbeat (C : List w64) (e : TraceEv) (id : w64) (s : NState)
    (cfg : CfgM) (m : Msg) (a : Etcdraft.Server)
    (hev : SendEvOf (W64 9) id s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : id ∈ C) (hdC : m.dst ∈ C)
    (hR : SimServerR C C.length (toPState s) a) (hs : LogShapeOk C.length (toPState s))
    (hrole : s.role = .leader) (hty : m.ty = .heartbeat) (hsrc : m.src = id) (hdst : m.dst ≠ id)
    (hterm : m.term = s.term) (hents : m.entries = [])
    (hcommit : uint.Z m.commit = min (uint.Z (toPState s).commit) (uint.Z (matchOf (toPState s) m.dst)))
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (bmc : uint.Z m.commit < 2 ^ 63) :
    LineEffect C false e (idAbs id) a a none _root_.id
      (fun b => b.with ((msgAbs C C.length m).get (by simp [msgAbs, hty]))) (fun _ => False) := by
  subst hsrc
  obtain ⟨hname, hnid, hterm', hvote, hcommit', hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  have hname' : gsStr e.name = "SendAppendEntriesRequest" := by
    simp only [evtNames] at hname
    have : e.name = go!"SendAppendEntriesRequest" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  have htyp : tm.typ = msgTypeStr .heartbeat := by rw [hm.1, hty]
  refine ⟨msgLine e m.src s.vote m.src m.dst xs,
    parseLine_msg 0 e m.src s.vote m.src m.dst xs [] tm hnid hvote hconf hmsg hm.2.2.1 hm.2.2.2.1
      (by rw [htyp]; rfl) (by rw [hname']; decide), rfl, ?_⟩
  intro t l pl σ hline hl0 hl hb hts _ hsrv hσi _ _ _ _ hfin
  have hhb := heartbeat_send σ C C.length (toPState s) m.src m (by rw [hσi]; exact hR)
    (by simp [toPState, hrole, proleRole]) hty rfl hdst hdC (by rw [hterm]; rfl) hcommit
  have hF : withNode σ (idAbs m.src) a _root_.id
      (fun b => b.with ((msgAbs C C.length m).get (by simp [msgAbs, hty]))) =
      σ.send ((msgAbs C C.length m).get (by simp [msgAbs, hty])) := by rw [← hσi, withNode_same]; rfl
  refine ⟨⟨σ.send ((msgAbs C C.length m).get (by simp [msgAbs, hty])), l + 1, l⟩, hF.symm,
    Chain.last _ _ _ ?_ rfl (by rw [← hF]; exact hfin)⟩
  · apply next_of_nonReceive _ ⟨σ, l, pl⟩ _ hl0 hl hb (by rw [hline]; simp [msgLine, evConv, hname']; rfl)
    apply nonReceive_heartbeat _ _ (idAbs m.src) (idAbs m.dst) _ hl
    · rw [hline]; simp [msgLine, evConv, hname']
    · rw [hline]; rfl
    · rw [hline]; rfl
    · rw [hline]; simp [msgLine, evConv, hmsg, htyp]; rfl
    · rw [hts]; exact confAbs_nodup C
    · rw [hts, mem_confAbs]; exact hC
    · rw [hts, mem_confAbs]; exact hdC
    · exact hhb
    · unfold Etcdraft.Trace.validateAfterAppendEntries Etcdraft.Trace.validatePostStates
      rw [hline, Bool.and_eq_true]
      constructor
      · have := stateMatches_node C s a e m.src xs hR hs (by rw [hrole]; decide) hterm' hcommit' hrl
          hlog (hxs.trans hin) bt bc bl σ hσi
          (by rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC)
        unfold Etcdraft.Line.stateMatches at this ⊢
        simpa [Etcdraft.State.send, msgLine, nodeLine] using this
      · apply newPending_send
        exact isAER_heartbeat C C.length e m.src s.vote xs m tm hmsg hm hty hents (by rw [hterm]; exact bt) bmc

/-- **The global step of a line with an effect** (the pure core of the global theorem): a run
reaching `σ`, node `i`'s server `a`, extended by a line `e` whose effect (`LineEffect`) holds,
given the conditions only the whole state knows (the line past the bootstrap, the skip bit, a
received message the only match) and the invariants at the intermediate and final states. -/
theorem simRun_lineEffect (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hrun : SimRun C L σ)
    (hσinv : σ.violated = .ok none) (e : TraceEv) (bf : Bool) (i : Etcdraft.ID) (a a' : Etcdraft.Server)
    (rcv : Option Etcdraft.Msg) (fM fP : Etcdraft.Bag → Etcdraft.Bag) (Mid : Etcdraft.Server → Prop)
    (hle : LineEffect C bf e i a a' rcv fM fP Mid)
    (hsrv : σ.server = confAbs C) (hσi : σ.s i = a) (hpv : σ.preVote = false) (hcq : σ.checkQuorum = false)
    (hboot : ∀ lines ln, parseLines (L.map evConv) = .ok lines → Etcdraft.parseLine 0 (evConv e) = .ok ln →
      (bootFlags (confAbs C) (lines ++ [ln])).getD L.length false = false)
    (hbf : ∀ lines ln pl, parseLines (L.map evConv) = .ok lines → Etcdraft.parseLine 0 (evConv e) = .ok ln →
      (linesTrace C (lines ++ [ln])).isBecomeFollowerInUpdateTermOrReturnToFollower ⟨σ, L.length + 1, pl⟩ = bf)
    (hrcv : ∀ ln, Etcdraft.parseLine 0 (evConv e) = .ok ln →
      match rcv with
      | none => True
      | some m => σ.messages.domain.Nodup ∧ m ∈ σ.messages.domain ∧ 0 < Etcdraft.Bag.count σ.messages m ∧
          ∀ m' ∈ σ.messages.domain, m' ≠ m → recvPred ln m' = false)
    (hmids : ∀ v, Mid v → (withNode σ i v _root_.id _root_.id).violated = .ok none)
    (hinv : (withNode σ i a' fM fP).violated = .ok none) :
    SimRun C (L ++ [e]) (withNode σ i a' fM fP) := by
  obtain ⟨ln, hparse, _, hall⟩ := hle
  by_cases hL : L = []
  · -- the run's first line, from the voters' initial state
    subst hL
    have hσ : σ = simInit C := by
      rcases hrun with ⟨-, h⟩ | ⟨lines, ts, hl, hr, hσ', -⟩
      · exact h
      · simp only [List.map_nil, List.length_nil] at hl hr
        cases hr
        rw [← hσ']; rfl
    subst hσ
    have hl0 : parseLines (([] : List TraceEv).map evConv) = .ok [] := by
      simp [parseLines, pure, Except.pure]
    obtain ⟨tsF, hF, hch⟩ := hall (linesTrace C [ln]) 1 0 (simInit C)
      (linesTrace_line_last C [] ln 1 rfl) (by omega) (by simp [linesTrace, Etcdraft.Trace.len])
      (by simp only [linesTrace]; simpa using hboot [] ln hl0 hparse) rfl (by simpa using hbf [] ln 0 hl0 hparse) hsrv hσi hpv hcq
      (by have h := hrcv ln hparse; revert h; cases rcv <;> exact id) hmids hinv
    have := simRun_first C e ln tsF _ hσinv (by simpa using parseLine_idx 0 0 _ _ hparse)
      (checkLine_of_chain _ ⟨simInit C, 1, 0⟩ tsF hch) rfl rfl
    rw [hF] at this
    simpa using this
  apply simRun_snoc_chain C L σ _ e ln hrun hL (parseLine_idx 0 _ _ _ hparse)
  intro lines ts hl hts hl'
  have hlen := parseLines_length _ _ hl
  simp only [List.length_map] at hlen
  obtain ⟨tl, tsl, tpl⟩ := ts
  simp only at hts hl'
  subst hts hl'
  exact hall (linesTrace C (lines ++ [ln])) (L.length + 1) tpl tl
    (linesTrace_line_last C lines ln _ (by omega)) (by omega) (by simp [linesTrace, Etcdraft.Trace.len]; omega)
    (by simp only [linesTrace]; simpa using hboot lines _ hl hparse) rfl (hbf lines ln tpl hl hparse) hsrv hσi hpv hcq
    (by have h := hrcv ln hparse; revert h; cases rcv <;> exact id) hmids hinv

/-- **A non-receive line's effect from its `nonReceive`**: a line whose `nonReceive` has, in every trace
and state where it could occur, the one successor `withNode σ i a' id fP` (no message consumed). -/
theorem lineEffect_nr (C : List w64) (bf : Bool) (e : TraceEv) (i : Etcdraft.ID) (a a' : Etcdraft.Server)
    (fP : Etcdraft.Bag → Etcdraft.Bag) (Mid : Etcdraft.Server → Prop) (ln : Etcdraft.Line)
    (hparse : Etcdraft.parseLine 0 (evConv e) = .ok ln) (hnid : ln.nid = i)
    (hrecv : Etcdraft.isReceiveName ln.ev.name = false)
    (hnr : ∀ (t : Etcdraft.Trace) (l pl : Nat) (σ : Etcdraft.State), t.line l = ln → l ≤ t.len →
      t.server = confAbs C → t.isBecomeFollowerInUpdateTermOrReturnToFollower ⟨σ, l, pl⟩ = bf →
      σ.server = confAbs C → σ.s i = a → σ.preVote = false → σ.checkQuorum = false →
      t.nonReceive ⟨σ, l, pl⟩ = .ok [withNode σ i a' _root_.id fP]) :
    LineEffect C bf e i a a' none _root_.id fP Mid := by
  refine ⟨ln, hparse, hnid, ?_⟩
  intro t l pl σ hline hl0 hl hb hts hbf hsrv hσi hpv hcq _ _ hfin
  refine ⟨⟨withNode σ i a' _root_.id fP, l + 1, l⟩, rfl, Chain.last _ _ _ ?_ rfl hfin⟩
  exact next_of_nonReceive _ ⟨σ, l, pl⟩ _ hl0 hl hb (by rw [hline]; exact hrecv)
    (hnr t l pl σ hline hl hts hbf hsrv hσi hpv hcq)

/-- **A `MsgApp` send's effect**: the leader's server unchanged, the request pending. -/
theorem lineEffect_msgApp (C : List w64) (e : TraceEv) (id : w64) (s : NState) (cfg : CfgM) (m : Msg)
    (a : Etcdraft.Server) (Mid : Etcdraft.Server → Prop)
    (hev : SendEvOf (W64 9) id s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : id ∈ C) (hdC : m.dst ∈ C)
    (hR : SimServerR C C.length (toPState s) a) (hs : LogShapeOk C.length (toPState s))
    (hrole : s.role = .leader) (hty : m.ty = .app) (hsrc : m.src = id) (hdst : m.dst ≠ id)
    (hterm : m.term = s.term) (hpk : uint.nat m.index + m.entries.length ≤ (toPState s).log.length)
    (hlt : plogTermAt (toPState s).base (toPState s).log m.index = some m.logterm)
    (hents : m.entries = ((toPState s).log.drop (uint.nat m.index)).take m.entries.length)
    (hcommit : m.commit = (toPState s).commit)
    (hmatch : uint.Z (matchOf (toPState s) m.dst) ≤ uint.Z m.index)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (bi : uint.Z m.index < 2 ^ 63)
    (blt : uint.Z m.logterm < 2 ^ 63) :
    LineEffect C false e (idAbs id) a a none _root_.id
      (fun b => b.with ((msgAbs C C.length m).get (by simp [msgAbs, hty]))) Mid := by
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
  have hidxZ : ((uint.nat m.index : Nat) : Int) = uint.Z m.index := by word
  have hk : gInt (W64 m.entries.length) = (m.entries.length : Int) := by
    rw [gInt_of_lt _ (by word)]; word
  apply lineEffect_nr C false e (idAbs id) a a _ Mid (msgLine e id s.vote m.src m.dst xs)
    (parseLine_msg 0 e id s.vote m.src m.dst xs [] tm hnid hvote hconf hmsg hm.2.2.1 hm.2.2.2.1
      (by rw [htyp]; rfl) (by rw [hname']; decide)) rfl (by simp [msgLine, evConv, hname']; rfl)
  intro t l pl σ hline hl hts _ hsrv hσi _ _
  have hae := appendEntries_send σ C C.length (toPState s) id m m.entries.length (by rw [hσi]; exact hR)
    (by simp [toPState, hrole, proleRole]) hs hty hsrc hdst hdC (by rw [hterm]; rfl) hpk hlt hents hcommit
  have hR6 := hR.2.2.2.2.2.1
  have hR11 := hR.2.2.2.2.2.2.2.2.2.2
  rw [← hσi, withNode_same]
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
    have hmi : (σ.s (idAbs id)).matchIndex (idAbs m.dst) = uint.Z (matchOf (toPState s) m.dst) := by
      rw [hσi]; exact hR11 (by simp [toPState, hrole, proleRole]) m.dst hdC
    have hll : ((σ.s (idAbs id)).log.length : Int) = (toPState s).log.length := by rw [hσi, hR6, logAbs_length]
    apply nonReceive_msgApp _ ⟨σ, l, pl⟩ (idAbs id) (idAbs m.dst) _ em hl
    · rw [hline]; simp [msgLine, evConv, hname']
    · rw [hline]; show idAbs m.src = idAbs id; rw [hsrc]
    · rw [hline]; rfl
    · rw [hline]; exact hc
    · exact hety
    · rw [hts]; exact confAbs_nodup C
    · rw [hts, mem_confAbs]; exact hC
    · rw [hts, mem_confAbs]; exact hdC
    · rw [hmi, heidx]; omega
    · rw [heidx, heent, hll]; omega
    · rw [hmi, heidx, heent]; omega
    · rw [heent]; omega
    · rw [heidx, heent, ← hidxZ]; exact hae
    · unfold Etcdraft.Trace.validateAfterAppendEntries Etcdraft.Trace.validatePostStates
      rw [hline, Bool.and_eq_true]
      constructor
      · have := stateMatches_node C s (σ.s (idAbs id)) e id xs (by rw [hσi]; exact hR)
          hs (by rw [hrole]; decide) hterm' hcommit' hrl hlog (hxs.trans hin) bt bc bl σ rfl
          (by rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC)
        unfold Etcdraft.Line.stateMatches at this ⊢
        simpa [Etcdraft.State.send, msgLine, nodeLine] using this
      · apply newPending_send
        have := isAER_app C C.length e id s.vote xs m tm hmsg hm hty (by rw [hterm]; exact bt)
          (by rw [hcommit]; simpa [toPState] using bc) bi blt (by omega)
        rw [hsrc] at this ⊢
        exact this

/-- **A vote request's send effect**: the candidate's server unchanged, the request pending. -/
theorem lineEffect_requestVote (C : List w64) (e : TraceEv) (id : w64) (s : NState) (cfg : CfgM) (m : Msg)
    (a : Etcdraft.Server) (Mid : Etcdraft.Server → Prop)
    (hev : SendEvOf (W64 13) id s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : id ∈ C) (hdC : m.dst ∈ C)
    (hR : SimServerR C C.length (toPState s) a) (hs : LogShapeOk C.length (toPState s))
    (hrole : s.role = .candidate) (hty : m.ty = .vote) (hsrc : m.src = id) (hdst : m.dst ≠ id)
    (hw : (toPState s).votes !! m.dst = none) (hterm : m.term = s.term)
    (hidx : m.index = (plogLast (toPState s).base (toPState s).log).index')
    (hlt : m.logterm = (plogLast (toPState s).base (toPState s).log).term')
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (bi : uint.Z m.index < 2 ^ 63)
    (blt : uint.Z m.logterm < 2 ^ 63) :
    LineEffect C false e (idAbs id) a a none _root_.id
      (fun b => b.with ((msgAbs C C.length m).get (by simp [msgAbs, hty]))) Mid := by
  obtain ⟨hname, hnid, hterm', hvote, hcommit', hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  have hname' : gsStr e.name = "SendRequestVoteRequest" := by
    simp only [evtNames] at hname
    have : e.name = go!"SendRequestVoteRequest" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  have htyp : tm.typ = msgTypeStr .vote := by rw [hm.1, hty]
  apply lineEffect_nr C false e (idAbs id) a a _ Mid (msgLine e id s.vote m.src m.dst xs)
    (parseLine_msg 0 e id s.vote m.src m.dst xs [] tm hnid hvote hconf hmsg hm.2.2.1 hm.2.2.2.1
      (by rw [htyp]; rfl) (by rw [hname']; decide)) rfl (by simp [msgLine, evConv, hname']; rfl)
  intro t l pl σ hline hl hts _ hsrv hσi hpv _
  have hrv := requestVote_send σ C C.length (toPState s) id m (by rw [hσi]; exact hR)
    (by simp [toPState, hrole, proleRole]) hs hty hsrc hdst hdC hw (by rw [hterm]; rfl) hidx hlt
  rw [← hσi, withNode_same]
  apply nonReceive_requestVote _ ⟨σ, l, pl⟩ (idAbs m.src) (idAbs m.dst) _ hl
  · rw [hline]; simp [msgLine, evConv, hname']
  · rw [hline]; rfl
  · rw [hline]; rfl
  · rw [hline]; simp [msgLine, evConv, hmsg]
  · rw [hts]; exact confAbs_nodup C
  · rw [hts, mem_confAbs, hsrc]; exact hC
  · rw [hts, mem_confAbs]; exact hdC
  · exact hpv
  · rw [hsrc]; exact hrv
  · rw [hline, hsrc]
    have := stateMatches_node C s (σ.s (idAbs id)) e id xs (by rw [hσi]; exact hR) hs (by rw [hrole]; decide)
      hterm' hcommit' hrl hlog (hxs.trans hin) bt bc bl σ rfl (by rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC)
    unfold Etcdraft.Line.stateMatches at this ⊢
    simpa [Etcdraft.State.send, msgLine, nodeLine] using this
  · rw [hline]
    apply newPending_send
    have := isRVReq_vote C C.length e id s.vote xs m tm hmsg hm hty (by rw [hterm]; exact bt) bi blt
    rw [hsrc] at this ⊢
    simp [this]

/-- **A one-round receive line's effect** (the line `ln` a receive matching `m`; in every state where
it could occur, `m`'s receipt has the one successor `withNode σ i a' fM fP`, consuming `m`, and the
line matches the node's state). -/
theorem lineEffect_recv1 (C : List w64) (bf : Bool) (e : TraceEv) (i : Etcdraft.ID) (a a' : Etcdraft.Server)
    (m : Etcdraft.Msg) (fM fP : Etcdraft.Bag → Etcdraft.Bag) (Mid : Etcdraft.Server → Prop) (ln : Etcdraft.Line)
    (hparse : Etcdraft.parseLine 0 (evConv e) = .ok ln) (hnid : ln.nid = i)
    (hrecv : Etcdraft.isReceiveName ln.ev.name = true) (hmatch : recvPred ln m = true) (hdest : m.dest = i)
    (hrcv : ∀ σ : Etcdraft.State, σ.server = confAbs C → σ.s i = a → σ.preVote = false → σ.checkQuorum = false →
      σ.messages.domain.Nodup → 0 < Etcdraft.Bag.count σ.messages m →
      ln.stateMatches σ i = true ∧ σ.receive m = .ok [withNode σ i a' fM fP] ∧
        Etcdraft.oneLessMessage σ (withNode σ i a' fM fP) m = true) :
    LineEffect C bf e i a a' (some m) fM fP Mid := by
  refine ⟨ln, hparse, hnid, ?_⟩
  intro t l pl σ hline hl0 hl hb hts _ hsrv hσi hpv hcq hrc _ hfin
  obtain ⟨hnd, hmem, hcnt, huniq⟩ := hrc
  obtain ⟨hsm, hr, hone⟩ := hrcv σ hsrv hσi hpv hcq hnd hcnt
  refine ⟨⟨withNode σ i a' fM fP, l + 1, l⟩, rfl, Chain.last _ _ _ ?_ rfl hfin⟩
  have := next_receive t ⟨σ, l, pl⟩ m (withNode σ i a' fM fP) hl0 hl hb (by rw [hline]; exact hrecv) hnd hmem
    (by rw [hline]; exact hmatch)
    (by unfold Etcdraft.Trace.validatePreStates; rw [hline, hdest, hsm]; simp)
    (fun m' hm' hne => by rw [hline]; simp [huniq m' hm' hne]) hr
  rw [this]; simp [recvNext, hone]

/-- **A reply's send effect**: none (the receive line queued it; the line is skipped). -/
theorem lineEffect_skipResp (C : List w64) (e : TraceEv) (id : w64) (s : NState) (cfg : CfgM) (m : Msg)
    (evt : w64) (a : Etcdraft.Server) (Mid : Etcdraft.Server → Prop)
    (hevt : evt = W64 11 ∨ evt = W64 15)
    (hev : SendEvOf evt id s cfg m e) (hout : cfg.outgoing = ∅) (hne : m.src ≠ m.dst)
    (htr : m.ty = .appResp ∨ m.ty = .heartbeatResp ∨ m.ty = .voteResp) :
    LineEffect C false e (idAbs id) a a none _root_.id _root_.id Mid := by
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
  apply lineEffect_nr C false e (idAbs id) a a _ Mid (msgLine e id s.vote m.src m.dst xs)
    (parseLine_msg 0 e id s.vote m.src m.dst xs [] tm hnid hvote hconf hmsg hm.2.2.1 hm.2.2.2.1
      htyp (by rcases hname' with h | h <;> rw [h] <;> decide)) rfl
    (by simp only [msgLine, evConv]; rcases hname' with h | h <;> rw [h] <;> rfl)
  intro t l pl σ hline hl _ _ _ hσi _ _
  have hσ : withNode σ (idAbs id) a _root_.id _root_.id = σ := by
    rw [← hσi]; unfold withNode
    have : (fun j => if j = idAbs id then σ.s (idAbs id) else σ.s j) = σ.s := by
      funext j; split <;> simp_all
    rw [this]; rfl
  rw [hσ]
  apply nonReceive_skipResp _ _ hl
  · rw [hline]; simpa [msgLine, evConv] using hname'
  · rw [hline]; exact hne'
  · rw [hline]
    refine ⟨_, by simp [msgLine, evConv, hmsg]; rfl, ?_⟩
    simp only [hm.2.2.1, hm.2.2.2.1]
    intro h
    exact hne' (by
      have h1 := parseID_decStr m.src; have h2 := parseID_decStr m.dst
      rw [h] at h1; rw [h1] at h2; exact Option.some.inj h2)

theorem upd_eq_withNode (σ : Etcdraft.State) (i : Etcdraft.ID) (f : Etcdraft.Server → Etcdraft.Server) :
    σ.upd i f = withNode σ i (f (σ.s i)) _root_.id _root_.id := rfl

/-- **A `Commit` line's effect**: the leader's `AdvanceCommitIndex`, to `n` (`AdvancesTo`). -/
theorem lineEffect_commit (C : List w64) (e : TraceEv) (id : w64) (s : NState) (cfg : CfgM)
    (a : Etcdraft.Server) (n : Int) (Mid : Etcdraft.Server → Prop)
    (hev : NodeEvOf rsmCommit id s cfg e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : id ∈ C) (hlead : a.state = Etcdraft.leader) (hadv : AdvancesTo a n)
    (hR : SimServerR C C.length (toPState s) { a with commitIndex := max a.commitIndex n })
    (hs : LogShapeOk C.length (toPState s)) (hrole : s.role = .leader)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) :
    LineEffect C false e (idAbs id) a { a with commitIndex := max a.commitIndex n } none _root_.id _root_.id Mid := by
  obtain ⟨hname, hnid, hterm, hvote, hcommit, hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, hmsg, -, -, -, -⟩ := hev
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  have hname' : gsStr e.name = "Commit" := by
    simp only [rsmCommit, evtNames] at hname
    have : e.name = go!"Commit" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  refine ⟨nodeLine e id s.vote xs,
    parseLine_node 0 e id s.vote xs [] hnid hvote hconf hmsg (by rw [hname']; rfl) (by rw [hname']; decide), rfl, ?_⟩
  intro t l pl σ hline hl0 hl hb hts _ hsrv hσi _ _ _ _ hfin
  have hF : withNode σ (idAbs id) { a with commitIndex := max a.commitIndex n } _root_.id _root_.id =
      σ.commitTo (idAbs id) n := by rw [Etcdraft.State.commitTo, upd_eq_withNode, hσi]
  refine ⟨⟨σ.commitTo (idAbs id) n, l + 1, l⟩, hF.symm, Chain.last _ _ _ ?_ rfl (by rw [← hF]; exact hfin)⟩
  apply next_commit t ⟨σ, l, pl⟩ (idAbs id) _ hl0 hl hb
  · rw [hline]; simp [nodeLine, evConv, hname']
  · rw [hline]; rfl
  · rw [hts]; exact confAbs_nodup C
  · rw [hts, mem_confAbs]; exact hC
  · exact hadv σ (idAbs id) hσi
  · rw [hline]
    apply stateMatches_node C s _ e id xs hR hs (by rw [hrole]; decide) hterm hcommit hrl hlog
      (hxs.trans hin) bt bc bl
    · simp [Etcdraft.State.commitTo, Etcdraft.State.upd, hσi]
    · simp only [Etcdraft.State.commitTo, Etcdraft.State.upd]; rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  · rw [hline]; simp only [nodeLine, evConv, hrl, hrole]; rfl
  · simp only; rw [hσi]; exact hlead

/-- **A `BecomeLeader` line's effect**: the candidate with a quorum of votes becomes leader. -/
theorem lineEffect_becomeLeader (C : List w64) (e : TraceEv) (id : w64) (s : NState) (cfg : CfgM)
    (a : Etcdraft.Server) (Mid : Etcdraft.Server → Prop)
    (hev : NodeEvOf (W64 3) id s cfg e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : id ∈ C) (hcand : a.state = Etcdraft.candidate) (hcfg : a.config.incoming = confAbs C)
    (hq : Etcdraft.isQuorum a.votesGranted (confAbs C) = true)
    (hR : SimServerR C C.length (toPState s) (leaderOf (idAbs id) a))
    (hs : LogShapeOk C.length (toPState s)) (hrole : s.role = .leader)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) :
    LineEffect C false e (idAbs id) a (leaderOf (idAbs id) a) none _root_.id _root_.id Mid := by
  obtain ⟨hname, hnid, hterm, hvote, hcommit, hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, hmsg, -, -, -, -⟩ := hev
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  have hname' : gsStr e.name = "BecomeLeader" := by
    simp only [evtNames] at hname
    have : e.name = go!"BecomeLeader" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  apply lineEffect_nr C false e (idAbs id) a _ _root_.id Mid (nodeLine e id s.vote xs)
    (parseLine_node 0 e id s.vote xs [] hnid hvote hconf hmsg (by rw [hname']; rfl) (by rw [hname']; decide)) rfl
    (by simp [nodeLine, evConv, hname']; rfl)
  intro t l pl σ hline hl hts _ hsrv hσi _ _
  have hbl : σ.becomeLeader (idAbs id) = some (σ.upd (idAbs id) (leaderOf (idAbs id))) := by
    unfold Etcdraft.State.becomeLeader Etcdraft.State.getConfig
    rw [hσi]; simp only [hcand, hcfg, hq, beq_self_eq_true, Bool.and_self, ↓reduceIte]
    rfl
  have hF : withNode σ (idAbs id) (leaderOf (idAbs id) a) _root_.id _root_.id = σ.upd (idAbs id) (leaderOf (idAbs id)) := by
    rw [upd_eq_withNode, hσi]
  rw [hF]
  apply nonReceive_becomeLeader _ _ (idAbs id) _ hl
  · rw [hline]; simp [nodeLine, evConv, hname']
  · rw [hline]; rfl
  · rw [hts]; exact confAbs_nodup C
  · rw [hts, mem_confAbs]; exact hC
  · exact hbl
  · rw [hline]
    apply stateMatches_node C s _ e id xs hR hs (by rw [hrole]; decide) hterm hcommit hrl hlog
      (hxs.trans hin) bt bc bl
    · rw [upd_self, hσi]
    · rw [upd_server, hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  · rw [hline]; simp only [nodeLine, evConv, hrl, hrole]; rfl
  · rw [upd_self]; rfl

/-- **A `Replicate` line's effect**: the leader's `ClientRequest`, an entry of its term appended. -/
theorem lineEffect_replicate (C : List w64) (e : TraceEv) (id : w64) (s : NState) (cfg : CfgM)
    (a : Etcdraft.Server) (Mid : Etcdraft.Server → Prop)
    (hev : NodeEvOf (W64 5) id s cfg e) (hout : cfg.outgoing = ∅)
    (hC : id ∈ C) (hlead : a.state = Etcdraft.leader) :
    LineEffect C false e (idAbs id) a
      { a with log := a.log ++ [{ term := a.currentTerm, type := .value, value := .val 0 }] }
      none _root_.id _root_.id Mid := by
  obtain ⟨hname, hnid, -, hvote, -, -, -, ⟨xs, ys, -, hys, hconf⟩, hmsg, -, -, -, -⟩ := hev
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  have hname' : gsStr e.name = "Replicate" := by
    simp only [evtNames] at hname
    have : e.name = go!"Replicate" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  apply lineEffect_nr C false e (idAbs id) a _ _root_.id Mid (nodeLine e id s.vote xs)
    (parseLine_node 0 e id s.vote xs [] hnid hvote hconf hmsg (by rw [hname']; rfl) (by rw [hname']; decide)) rfl
    (by simp [nodeLine, evConv, hname']; rfl)
  intro t l pl σ hline hl hts _ hsrv hσi _ _
  have hcr : σ.clientRequest (idAbs id) 0 = some (σ.replicate (idAbs id) (.val 0) .value) := by
    unfold Etcdraft.State.clientRequest; simp [hσi, hlead]
  have hF : withNode σ (idAbs id) { a with log := a.log ++ [{ term := a.currentTerm, type := .value, value := .val 0 }] }
      _root_.id _root_.id = σ.replicate (idAbs id) (.val 0) .value := by
    rw [Etcdraft.State.replicate, upd_eq_withNode, hσi]
  rw [hF]
  apply nonReceive_replicate _ _ (idAbs id) _ hl
  · rw [hline]; simp [nodeLine, evConv, hname']
  · rw [hline]; rfl
  · rw [hts]; exact confAbs_nodup C
  · rw [hts, mem_confAbs]; exact hC
  · exact hcr

/-- **A `BecomeCandidate` line's effect**: the specification's `Timeout` (pre-vote off). -/
theorem lineEffect_becomeCandidate (C : List w64) (e : TraceEv) (id : w64) (s : NState) (cfg : CfgM)
    (a : Etcdraft.Server) (Mid : Etcdraft.Server → Prop)
    (hev : NodeEvOf (W64 1) id s cfg e) (hout : cfg.outgoing = ∅)
    (hC : id ∈ C) (hrl : a.state = Etcdraft.follower ∨ a.state = Etcdraft.candidate)
    (hcfg : a.config.incoming = confAbs C)
    (hrole : s.role = .candidate) (hterm : a.currentTerm + 1 = uint.Z s.term) (bt : uint.Z s.term < 2 ^ 63) :
    LineEffect C false e (idAbs id) a (candOf (idAbs id) a) none _root_.id _root_.id Mid := by
  obtain ⟨hname, hnid, hterm', hvote, -, hrl', -, ⟨xs, ys, -, hys, hconf⟩, hmsg, -, -, -, -⟩ := hev
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  have hname' : gsStr e.name = "BecomeCandidate" := by
    simp only [evtNames] at hname
    have : e.name = go!"BecomeCandidate" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  apply lineEffect_nr C false e (idAbs id) a _ _root_.id Mid (nodeLine e id s.vote xs)
    (parseLine_node 0 e id s.vote xs [] hnid hvote hconf hmsg (by rw [hname']; rfl) (by rw [hname']; decide)) rfl
    (by simp [nodeLine, evConv, hname']; rfl)
  intro t l pl σ hline hl hts _ hsrv hσi hpv _
  have hto : σ.timeout (idAbs id) = some (σ.upd (idAbs id) (candOf (idAbs id))) := by
    unfold Etcdraft.State.timeout Etcdraft.State.timeoutEnabled Etcdraft.Server.timeoutRoleOk
      Etcdraft.State.getConfig
    have hcont : (confAbs C).contains (idAbs id) = true := by
      rw [List.contains_iff_mem, mem_confAbs]; exact hC
    rw [hσi]
    rcases hrl with h | h <;> simp only [h, hcfg, hcont, hpv, beq_self_eq_true, Bool.true_or, Bool.or_true,
      Bool.true_and, Bool.not_false, ↓reduceIte] <;> rfl
  have hF : withNode σ (idAbs id) (candOf (idAbs id) a) _root_.id _root_.id = σ.upd (idAbs id) (candOf (idAbs id)) := by
    rw [upd_eq_withNode, hσi]
  rw [hF]
  apply nonReceive_becomeCandidate _ _ (idAbs id) _ hl
  · rw [hline]; simp [nodeLine, evConv, hname']
  · rw [hline]; rfl
  · rw [hts]; exact confAbs_nodup C
  · rw [hts, mem_confAbs]; exact hC
  · exact hto
  · rw [hline]; simp only [nodeLine, evConv, hrl', hrole]; rfl
  · rw [upd_self]; rfl
  · rw [upd_self, hline, hσi]; simp only [candOf, nodeLine, evConv, hterm']; rw [gInt_of_lt _ bt, hterm]

/-- **The candidate's own vote's send effect**: the self-addressed granted vote pending. -/
theorem lineEffect_selfVote (C : List w64) (e : TraceEv) (id : w64) (s : NState) (cfg : CfgM) (m : Msg)
    (a : Etcdraft.Server) (Mid : Etcdraft.Server → Prop)
    (hev : SendEvOf (W64 15) id s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : id ∈ C) (hR : SimServerR C C.length (toPState s) a) (hs : LogShapeOk C.length (toPState s))
    (hrole : s.role = .candidate) (hty : m.ty = .voteResp) (hsrc : m.src = id) (hdst : m.dst = id)
    (hw : (toPState s).votes !! id = none) (hterm : m.term = s.term) (hrej : m.reject = false)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) :
    LineEffect C false e (idAbs id) a a none _root_.id
      (fun b => b.with ((msgAbs C C.length m).get (by simp [msgAbs, hty]))) Mid := by
  obtain ⟨hname, hnid, hterm', hvote, hcommit', hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  have hname' : gsStr e.name = "SendRequestVoteResponse" := by
    simp only [evtNames] at hname
    have : e.name = go!"SendRequestVoteResponse" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  have htyp : tm.typ = msgTypeStr .voteResp := by rw [hm.1, hty]
  apply lineEffect_nr C false e (idAbs id) a a _ Mid (msgLine e id s.vote m.src m.dst xs)
    (parseLine_msg 0 e id s.vote m.src m.dst xs [] tm hnid hvote hconf hmsg hm.2.2.1 hm.2.2.2.1
      (by rw [htyp]; rfl) (by rw [hname']; decide)) rfl (by simp [msgLine, evConv, hname']; rfl)
  intro t l pl σ hline hl hts _ hsrv hσi hpv _
  have hrv := requestVoteSelf_send σ C C.length (toPState s) id m (by rw [hσi]; exact hR)
    (by simp [toPState, hrole, proleRole]) hty hsrc hdst hC hw (by rw [hterm]; rfl) hrej
  rw [← hσi, withNode_same]
  apply nonReceive_selfVote _ ⟨σ, l, pl⟩ (idAbs id) _ hl
  · rw [hline]; simp [msgLine, evConv, hname']
  · rw [hline, hsrc]; rfl
  · rw [hline, hdst]; rfl
  · rw [hline]
    refine ⟨_, by simp [msgLine, evConv, hmsg]; rfl, ?_⟩
    simp only [hm.2.2.1, hm.2.2.2.1, hsrc, hdst]
  · rw [hts]; exact confAbs_nodup C
  · rw [hts, mem_confAbs]; exact hC
  · exact hpv
  · exact hrv
  · rw [hline]
    have := stateMatches_node C s (σ.s (idAbs id)) e id xs (by rw [hσi]; exact hR) hs (by rw [hrole]; decide)
      hterm' hcommit' hrl hlog (hxs.trans hin) bt bc bl σ rfl
      (by rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC)
    unfold Etcdraft.Line.stateMatches at this ⊢
    simpa [Etcdraft.State.send, msgLine, nodeLine] using this
  · rw [hline]
    apply newPending_send
    have := isRVResp_voteResp C C.length e id s.vote xs m tm hmsg hm hty (by rw [hterm]; exact bt)
    have hsd : ((msgAbs C C.length m).get (by simp [msgAbs, hty])).source =
        ((msgAbs C C.length m).get (by simp [msgAbs, hty])).dest := by
      simp [msgAbs, hty, hsrc, hdst]
    simp [this, hsd]

/-- **The leader's own acknowledgement's send effect**: the self-addressed response pending. -/
theorem lineEffect_selfAck (C : List w64) (e : TraceEv) (id : w64) (s : NState) (cfg : CfgM)
    (a : Etcdraft.Server) (Mid : Etcdraft.Server → Prop)
    (hev : SendEvOf (W64 11) id s cfg (pselfAck id (toPState s)) e) (hin : (elements cfg.incoming).Perm C)
    (hout : cfg.outgoing = ∅) (hC : id ∈ C)
    (hR : SimServerR C C.length (toPState s) a) (hs : LogShapeOk C.length (toPState s))
    (hrole : s.role = .leader)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) :
    LineEffect C false e (idAbs id) a a none _root_.id
      (fun b => b.with ((msgAbs C C.length (pselfAck id (toPState s))).get (by simp [msgAbs, pselfAck]))) Mid := by
  obtain ⟨hname, hnid, hterm', hvote, hcommit', hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  have hname' : gsStr e.name = "SendAppendEntriesResponse" := by
    simp only [evtNames] at hname
    have : e.name = go!"SendAppendEntriesResponse" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  have htyp : tm.typ = msgTypeStr .appResp := by rw [hm.1]; rfl
  apply lineEffect_nr C false e (idAbs id) a a _ Mid (msgLine e id s.vote id id xs)
    (parseLine_msg 0 e id s.vote id id xs [] tm hnid hvote hconf hmsg hm.2.2.1 hm.2.2.2.1
      (by rw [htyp]; rfl) (by rw [hname']; decide)) rfl (by simp [msgLine, evConv, hname']; rfl)
  intro t l pl σ hline hl hts _ hsrv hσi _ _
  have hae := appendEntriesToSelf_send σ C C.length (toPState s) id (by rw [hσi]; exact hR)
    (by simp [toPState, hrole, proleRole]) hs
  rw [← hσi, withNode_same]
  apply nonReceive_selfAck _ ⟨σ, l, pl⟩ (idAbs id) _ hl
  · rw [hline]; simp [msgLine, evConv, hname']
  · rw [hline]; rfl
  · rw [hline]; rfl
  · rw [hline]
    refine ⟨_, by simp [msgLine, evConv, hmsg]; rfl, ?_⟩
    simp only [hm.2.2.1, hm.2.2.2.1]; rfl
  · rw [hts]; exact confAbs_nodup C
  · rw [hts, mem_confAbs]; exact hC
  · exact hae
  · rw [hline]
    have := stateMatches_node C s (σ.s (idAbs id)) e id xs (by rw [hσi]; exact hR) hs (by rw [hrole]; decide)
      hterm' hcommit' hrl hlog (hxs.trans hin) bt bc bl σ rfl
      (by rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC)
    unfold Etcdraft.Line.stateMatches at this ⊢
    simpa [Etcdraft.State.send, msgLine, nodeLine] using this
  · rw [hline]
    apply newPending_send
    have := isAEResp_appResp C C.length e id s.vote xs (pselfAck id (toPState s)) tm hmsg hm rfl rfl
      (by simp [pselfAck, toPState]; exact bt) (by simpa [pselfAck] using bl)
    simp only [msgAbs, pselfAck, Option.get_some] at this
    simp only [msgAbs, pselfAck, Option.get_some, Bool.and_eq_true, beq_self_eq_true, and_true]
    exact this

/-- The server a response of its term makes (`respSt`'s, as a function of the server). -/
def respSrv (v : Etcdraft.Server) (m : Etcdraft.Msg) : Etcdraft.Server :=
  if m.type = .requestVoteResponse then
    { v with votesResponded := v.votesResponded.add m.source,
             votesGranted := if m.voteGranted then v.votesGranted.add m.source else v.votesGranted }
  else if m.success then
    { v with matchIndex := fun k => if k = m.source then max (v.matchIndex m.source) m.matchIndex else v.matchIndex k }
  else v

theorem respSt_eq (σ : Etcdraft.State) (m : Etcdraft.Msg) :
    respSt σ m = withNode σ m.dest (respSrv (σ.s m.dest) m) (fun b => b.without m) _root_.id := by
  unfold respSt respSrv
  by_cases h1 : m.type = .requestVoteResponse
  · simp only [h1, ↓reduceIte]; rfl
  · simp only [h1, ↓reduceIte]
    by_cases h2 : m.success = true
    · simp only [h2, ↓reduceIte]; rfl
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      unfold withNode Etcdraft.State.discard
      have : (fun j => if j = m.dest then σ.s m.dest else σ.s j) = σ.s := by
        funext j; split <;> simp_all
      rw [this]; rfl

/-- **A response of the node's term's effect** (any role but pre-candidate). -/
theorem lineEffect_resp (C : List w64) (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg) (evt : w64)
    (a : Etcdraft.Server) (mabs : Etcdraft.Msg) (Mid : Etcdraft.Server → Prop)
    (htyev : (m.ty = .appResp ∧ evt = W64 12) ∨ (m.ty = .voteResp ∧ evt = W64 16))
    (hev : SendEvOf evt m.dst s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : m.dst ∈ C) (hR : SimServerR C C.length (toPState s) a) (hs : LogShapeOk C.length (toPState s))
    (hpre : s.role ≠ .preCandidate) (hterm : m.term = s.term)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (bi : uint.Z m.index < 2 ^ 63)
    (hmabs : msgAbs C C.length m = some mabs) :
    LineEffect C false e (idAbs m.dst) a (respSrv a mabs) (some mabs) (fun b => b.without mabs) _root_.id Mid := by
  have hev' := hev
  obtain ⟨hname, hnid, hterm', hvote, hcommit', hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev'
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  obtain ⟨nm, hname', hrn, htyp, hmt, hmdst, hmterm, hpred⟩ :=
    respLine C e s cfg m evt htyev hname tm hmsg hm (by rw [hterm]; exact bt) bi mabs hmabs
  have hparse : Etcdraft.parseLine 0 (evConv e) = .ok (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) := by
    rw [← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    exact parseLine_msg 0 e m.dst s.vote m.src m.dst xs [] tm hnid hvote hconf hmsg hm.2.2.1 hm.2.2.2.1
      (by rw [hm.1]; exact htyp)
      (by rw [hname']; intro h; rw [h] at hrn; exact absurd hrn (by decide))
  apply lineEffect_recv1 C false e (idAbs m.dst) a _ mabs _ _ Mid _ hparse rfl
    (by simp only [msgLine, evConv]; rw [hname']; exact hrn) hpred hmdst
  intro σ hsrv hσi _ _ hnd hcnt
  have hcontains : σ.server.contains (idAbs m.dst) = true := by
    rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  have hnp : (σ.s mabs.dest).state ≠ Etcdraft.preCandidate := by
    rw [hmdst, hσi, hR.2.1]; exact roleAbs_ne_pre _
  have heq : respSt σ mabs = withNode σ (idAbs m.dst) (respSrv a mabs) (fun b => b.without mabs) _root_.id := by
    rw [respSt_eq, hmdst, hσi]
  refine ⟨?_, ?_, ?_⟩
  · rw [← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    have hsm := stateMatches_node C s (σ.s (idAbs m.dst)) e m.dst xs (by rw [hσi]; exact hR) hs hpre hterm'
      hcommit' hrl hlog (hxs.trans hin) bt bc bl σ rfl hcontains
    unfold Etcdraft.Line.stateMatches at hsm ⊢
    simpa [msgLine, nodeLine] using hsm
  · rw [← heq]
    exact receive_resp σ mabs (by rw [hmdst]; exact hcontains) hmt (by rw [hmdst, hσi, hR.1, hmterm, hterm]; rfl) hnp
  · rw [← heq]; exact oneLess_resp σ mabs hnd hcnt

/-- Whether a vote request is granted (`HandleRequestVoteRequest`'s `grant`). -/
def vrGrant (v : Etcdraft.Server) (j : Etcdraft.ID) (m : Etcdraft.Msg) : Bool :=
  (m.term == v.currentTerm && (or (decide (m.lastLogTerm > Etcdraft.lastTerm v.log))
    (m.lastLogTerm == Etcdraft.lastTerm v.log && decide (m.lastLogIndex ≥ v.log.length))) &&
    (or (v.votedFor == j) (v.votedFor == Etcdraft.nil && v.lead == Etcdraft.nil)))

/-- The server after a vote request. -/
def vrSrv (v : Etcdraft.Server) (j : Etcdraft.ID) (m : Etcdraft.Msg) : Etcdraft.Server :=
  if vrGrant v j m then { v with votedFor := j } else v

/-- The response to a vote request. -/
def vrResp (v : Etcdraft.Server) (i j : Etcdraft.ID) (m : Etcdraft.Msg) : Etcdraft.Msg :=
  { type := .requestVoteResponse, term := v.currentTerm, voteGranted := vrGrant v j m, source := i, dest := j }

theorem voteReqResult_eq (σ : Etcdraft.State) (i j : Etcdraft.ID) (m : Etcdraft.Msg)
    (hle : m.term ≤ (σ.s i).currentTerm) :
    voteReqResult σ i j m =
      withNode σ i (vrSrv (σ.s i) j m) (fun b => b.without m) (fun b => b.with (vrResp (σ.s i) i j m)) := by
  unfold voteReqResult Etcdraft.State.handleRequestVoteRequest
  have hc : (!decide (m.term ≤ (σ.s i).currentTerm)) = false := by simp [hle]
  simp only [hc, Bool.false_eq_true, ↓reduceIte, Option.getD_some]
  unfold vrSrv vrResp vrGrant
  split
  · rename_i h; simp only [h]; rfl
  · rename_i h
    simp only [Bool.not_eq_true] at h
    simp only [h]
    unfold withNode Etcdraft.State.reply
    have : (fun k => if k = i then σ.s i else σ.s k) = σ.s := by funext k; split <;> simp_all
    rw [this]

/-- **A vote request of the node's term's effect** (`HandleRequestVoteRequest`, one round). -/
theorem lineEffect_voteReq (C : List w64) (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg)
    (a : Etcdraft.Server) (mabs : Etcdraft.Msg) (Mid : Etcdraft.Server → Prop)
    (hev : SendEvOf (W64 14) m.dst s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : m.dst ∈ C) (hR : SimServerR C C.length (toPState s) a) (hs : LogShapeOk C.length (toPState s))
    (hpre : s.role ≠ .preCandidate) (hty : m.ty = .vote) (hterm : m.term = s.term)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (bi : uint.Z m.index < 2 ^ 63)
    (blt : uint.Z m.logterm < 2 ^ 63) (hmabs : msgAbs C C.length m = some mabs) :
    LineEffect C false e (idAbs m.dst) a (vrSrv a (idAbs m.src) mabs) (some mabs) (fun b => b.without mabs)
      (fun b => b.with (vrResp a (idAbs m.dst) (idAbs m.src) mabs)) Mid := by
  have hev' := hev
  obtain ⟨hname, hnid, hterm', hvote, hcommit', hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev'
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  have hname' := (recvName_of _ e hname).2.2.1 rfl
  have hparse : Etcdraft.parseLine 0 (evConv e) = .ok (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) := by
    rw [← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    exact parseLine_msg 0 e m.dst s.vote m.src m.dst xs [] tm hnid hvote hconf hmsg hm.2.2.1 hm.2.2.2.1
      (by rw [hm.1, hty]; rfl) (by rw [hname']; decide)
  have hmt : mabs.type = .requestVoteRequest := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmdst : mabs.dest = idAbs m.dst := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmsrc : mabs.source = idAbs m.src := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmterm : mabs.term = uint.Z m.term := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hpred : recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) mabs = true := by
    rw [recvPred_rvreq _ _ (by rw [msgLine_name, hname'])]
    have := isRVReq_vote C C.length e m.dst s.vote (elements cfg.incoming) m tm hmsg hm hty
      (by rw [hterm]; exact bt) bi blt
    simp only [hmabs, Option.get_some] at this; exact this
  apply lineEffect_recv1 C false e (idAbs m.dst) a _ mabs _ _ Mid _ hparse rfl
    (by simp only [msgLine, evConv]; rw [hname']; rfl) hpred hmdst
  intro σ hsrv hσi _ _ hnd hcnt
  have hcontains : σ.server.contains (idAbs m.dst) = true := by
    rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  have hcur : mabs.term = (σ.s mabs.dest).currentTerm := by rw [hmdst, hσi, hR.1, hmterm, hterm]; rfl
  have heq : voteReqResult σ mabs.dest mabs.source mabs =
      withNode σ (idAbs m.dst) (vrSrv a (idAbs m.src) mabs) (fun b => b.without mabs)
        (fun b => b.with (vrResp a (idAbs m.dst) (idAbs m.src) mabs)) := by
    rw [voteReqResult_eq σ _ _ mabs (by rw [hcur]; exact Int.le_refl _), hmdst, hmsrc, hσi]
  refine ⟨?_, ?_, ?_⟩
  · rw [← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    have hsm := stateMatches_node C s (σ.s (idAbs m.dst)) e m.dst xs (by rw [hσi]; exact hR) hs hpre hterm'
      hcommit' hrl hlog (hxs.trans hin) bt bc bl σ rfl hcontains
    unfold Etcdraft.Line.stateMatches at hsm ⊢
    simpa [msgLine, nodeLine] using hsm
  · rw [← heq]
    exact receive_voteReq σ mabs (by rw [hmdst]; exact hcontains) hmt hcur
  · rw [← heq]
    exact oneLess_voteReq σ _ _ mabs (by rw [hcur]; exact Int.le_refl _) hnd hcnt

theorem withLead_reply_upd (σ : Etcdraft.State) (i j : Etcdraft.ID) (f : Etcdraft.Server → Etcdraft.Server)
    (r m : Etcdraft.Msg) :
    withLead ((σ.upd i f).reply r m) i j =
      withNode σ i { f (σ.s i) with lead := j } (fun b => b.without m) (fun b => b.with r) := by
  unfold withLead withNode Etcdraft.State.reply Etcdraft.State.upd
  simp only
  congr 1
  funext k; by_cases hk : k = i <;> simp [hk]

theorem withLead_reply (σ : Etcdraft.State) (i j : Etcdraft.ID) (r m : Etcdraft.Msg) :
    withLead (σ.reply r m) i j =
      withNode σ i { σ.s i with lead := j } (fun b => b.without m) (fun b => b.with r) := by
  have := withLead_reply_upd σ i j _root_.id r m
  have hσ : σ.upd i _root_.id = σ := by
    unfold Etcdraft.State.upd
    have : (fun k => if k = i then _root_.id (σ.s i) else σ.s k) = σ.s := by funext k; split <;> simp_all
    rw [this]
  rw [hσ] at this; exact this

/-- An append request's line: its name, its parse, and its predicate as `isAppendEntriesRequest`. -/
theorem aerParse (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg) (tm : TraceMsg)
    (hname : evtNames[uint.nat (W64 10)]? = some e.name) (hnid : e.nid = decStr m.dst)
    (hvote : e.vote = decStr s.vote) (xs : List w64) (hxs : xs.Perm (elements cfg.incoming))
    (hconf : e.conf = (xs.map decStr, ([] : List w64).map decStr)) (hmsg : e.msg = some tm)
    (hm : MsgEvOf m tm) (hty : m.ty = .app ∨ m.ty = .heartbeat) :
    Etcdraft.parseLine 0 (evConv e) = .ok (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) := by
  obtain ⟨hname', -, -⟩ := aerLine e s cfg m hname
  rw [← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
  exact parseLine_msg 0 e m.dst s.vote m.src m.dst xs [] tm hnid hvote hconf hmsg hm.2.2.1 hm.2.2.2.1
    (by rw [hm.1]; rcases hty with h | h <;> rw [h] <;> rfl) (by rw [hname']; decide)

/-- A heartbeat's receiver after it. -/
def hbSrv (a : Etcdraft.Server) (j : Etcdraft.ID) (c : Int) : Etcdraft.Server :=
  { a with commitIndex := max a.commitIndex c, lead := j }

/-- A heartbeat's response. -/
def hbResp (a : Etcdraft.Server) (i j : Etcdraft.ID) : Etcdraft.Msg :=
  { type := .appendEntriesResponse, subtype := "heartbeat", term := a.currentTerm, success := true, matchIndex := 0, source := i, dest := j }

/-- **A heartbeat of the node's term at a follower: its effect** (commit, lead, the reply). -/
theorem lineEffect_heartbeatRecv (C : List w64) (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg)
    (a : Etcdraft.Server) (mabs : Etcdraft.Msg) (Mid : Etcdraft.Server → Prop) (hty : m.ty = .heartbeat)
    (hev : SendEvOf (W64 10) m.dst s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : m.dst ∈ C) (hR : SimServerR C C.length (toPState s) a) (hs : LogShapeOk C.length (toPState s))
    (hrole : s.role = .follower) (hterm : m.term = s.term) (hents : m.entries = [])
    (hc1 : 1 ≤ uint.Z (toPState s).commit)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (bmc : uint.Z m.commit < 2 ^ 63)
    (hmabs : msgAbs C C.length m = some mabs) :
    LineEffect C false e (idAbs m.dst) a (hbSrv a (idAbs m.src) mabs.commitIndex)
      (some mabs) (fun b => b.without mabs) (fun b => b.with (hbResp a (idAbs m.dst) (idAbs m.src))) Mid := by
  have hev' := hev
  obtain ⟨hname, hnid, hterm', hvote, hcommit', hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev'
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  obtain ⟨hname', hrn, hrp⟩ := aerLine e s cfg m hname
  have hmt : mabs.type = .appendEntriesRequest := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmsub : mabs.subtype = "heartbeat" := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmterm : mabs.term = uint.Z m.term := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmprev : mabs.prevLogIndex = 0 := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hments : mabs.entries = [] := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmdst : mabs.dest = idAbs m.dst := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmsrc : mabs.source = idAbs m.src := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hpred : recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) mabs = true := by
    rw [hrp, ← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    have := isAER_heartbeat C C.length e m.dst s.vote xs m tm hmsg hm hty hents (by rw [hterm]; exact bt) bmc
    simp only [hmabs, Option.get_some] at this; exact this
  apply lineEffect_recv1 C false e (idAbs m.dst) a _ mabs _ _ Mid _
    (aerParse e s cfg m tm hname hnid hvote xs hxs hconf hmsg hm (Or.inr hty)) rfl
    (by simp only [msgLine, evConv]; rw [hname']; rfl) hpred hmdst
  intro σ hsrv hσi _ _ hnd hcnt
  have hcontains : σ.server.contains (idAbs m.dst) = true := by
    rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  have heq : hbRecvSt σ mabs = withNode σ (idAbs m.dst) (hbSrv a (idAbs m.src) mabs.commitIndex)
      (fun b => b.without mabs) (fun b => b.with (hbResp a (idAbs m.dst) (idAbs m.src))) := by
    unfold hbRecvSt Etcdraft.State.commitTo
    rw [hmdst, hmsrc, hσi]
    have := withLead_reply_upd σ (idAbs m.dst) (idAbs m.src)
      (fun v => { v with commitIndex := max v.commitIndex mabs.commitIndex })
      (hbResp a (idAbs m.dst) (idAbs m.src)) mabs
    rw [hσi] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · rw [← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    have hsm := stateMatches_node C s (σ.s (idAbs m.dst)) e m.dst xs (by rw [hσi]; exact hR) hs
      (by rw [hrole]; decide) hterm' hcommit' hrl hlog (hxs.trans hin) bt bc bl σ rfl hcontains
    unfold Etcdraft.Line.stateMatches at hsm ⊢
    simpa [msgLine, nodeLine] using hsm
  · rw [← heq]
    have := receive_heartbeat σ mabs (by rw [hmdst]; exact hcontains) hmt
      (by rw [hmdst, hσi, hR.2.1]; simp [toPState, hrole, proleRole]; rfl)
      (by rw [hmdst, hσi, hR.1, hmterm, hterm]; rfl) hmsub hmprev hments
      (by rw [hmdst, hσi, hR.2.2.2.2.2.2.1]; omega)
    rw [this]; rfl
  · rw [← heq]; exact oneLess_of_msgs σ _ mabs (by rfl) hnd hcnt

/-- A stale append request's response. -/
def stResp (a : Etcdraft.Server) (i j : Etcdraft.ID) (sub : String) : Etcdraft.Msg :=
  { type := .appendEntriesResponse, subtype := sub, term := a.currentTerm, success := true, matchIndex := a.commitIndex, source := i, dest := j }

/-- A rejected append request's response. -/
def rjResp (a : Etcdraft.Server) (i j : Etcdraft.ID) : Etcdraft.Msg :=
  { type := .appendEntriesResponse, subtype := "app", term := a.currentTerm, success := false, matchIndex := 0, source := i, dest := j }

/-- **A stale append request's effect** (its index below the commit index, the log matching). -/
theorem lineEffect_staleRecv (C : List w64) (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg)
    (a : Etcdraft.Server) (mabs : Etcdraft.Msg) (Mid : Etcdraft.Server → Prop) (hty : m.ty = .app)
    (hev : SendEvOf (W64 10) m.dst s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : m.dst ∈ C) (hR : SimServerR C C.length (toPState s) a) (hs : LogShapeOk C.length (toPState s))
    (hrole : s.role = .follower) (hterm : m.term = s.term)
    (hst : uint.Z m.index < uint.Z (toPState s).commit)
    (hmt0 : PlogMatches (entryID.mk (W64 0) (W64 0)) (toPState s).log (entryID.mk m.logterm (W64 (uint.nat m.index))))
    (hlt0 : uint.nat m.index = 0 → m.logterm = W64 0)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (bmc : uint.Z m.commit < 2 ^ 63)
    (bi : uint.Z m.index < 2 ^ 63) (blt : uint.Z m.logterm < 2 ^ 63) (bk : m.entries.length < 2 ^ 63)
    (hmabs : msgAbs C C.length m = some mabs) :
    LineEffect C false e (idAbs m.dst) a { a with lead := idAbs m.src } (some mabs) (fun b => b.without mabs)
      (fun b => b.with (stResp a (idAbs m.dst) (idAbs m.src) "app")) Mid := by
  have hev' := hev
  obtain ⟨hname, hnid, hterm', hvote, hcommit', hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev'
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  obtain ⟨hname', hrn, hrp⟩ := aerLine e s cfg m hname
  have hmt : mabs.type = .appendEntriesRequest := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmsub : mabs.subtype = "app" := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmterm : mabs.term = uint.Z m.term := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hidxZ : ((uint.nat m.index : Nat) : Int) = uint.Z m.index := by word
  have hmprev : mabs.prevLogIndex = (uint.nat m.index : Nat) := by
    rw [hidxZ]; simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmpt : mabs.prevLogTerm = uint.Z m.logterm := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmdst : mabs.dest = idAbs m.dst := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmsrc : mabs.source = idAbs m.src := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hpred : recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) mabs = true := by
    rw [hrp, ← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    have := isAER_app C C.length e m.dst s.vote xs m tm hmsg hm hty (by rw [hterm]; exact bt) bmc bi blt bk
    simp only [hmabs, Option.get_some] at this; exact this
  apply lineEffect_recv1 C false e (idAbs m.dst) a _ mabs _ _ Mid _
    (aerParse e s cfg m tm hname hnid hvote xs hxs hconf hmsg hm (Or.inl hty)) rfl
    (by simp only [msgLine, evConv]; rw [hname']; rfl) hpred hmdst
  intro σ hsrv hσi _ _ hnd hcnt
  have hcontains : σ.server.contains (idAbs m.dst) = true := by
    rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  have heq : staleRecvSt σ mabs = withNode σ (idAbs m.dst) { a with lead := idAbs m.src }
      (fun b => b.without mabs) (fun b => b.with (stResp a (idAbs m.dst) (idAbs m.src) "app")) := by
    unfold staleRecvSt
    rw [hmdst, hmsrc, hmsub, hσi]
    have := withLead_reply σ (idAbs m.dst) (idAbs m.src) (stResp a (idAbs m.dst) (idAbs m.src) "app") mabs
    rw [hσi] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · rw [← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    have hsm := stateMatches_node C s (σ.s (idAbs m.dst)) e m.dst xs (by rw [hσi]; exact hR) hs
      (by rw [hrole]; decide) hterm' hcommit' hrl hlog (hxs.trans hin) bt bc bl σ rfl hcontains
    unfold Etcdraft.Line.stateMatches at hsm ⊢
    simpa [msgLine, nodeLine] using hsm
  · rw [← heq]
    have hlok : LogOkL mabs (σ.s mabs.dest).log = true := by
      rw [hmdst, hσi, hR.2.2.2.2.2.1, logOkL_abs C C.length mabs _ (uint.nat m.index) m.logterm hmprev hmpt
        (fun k x hk hx => hs.2.2 k x (by omega) hx) hlt0 (by word), decide_eq_true_iff]
      exact hmt0
    have := receive_appStale σ mabs (by rw [hmdst]; exact hcontains) hmt
      (by rw [hmdst, hσi, hR.2.1]; simp [toPState, hrole, proleRole]; rfl)
      (by rw [hmdst, hσi, hR.1, hmterm, hterm]; rfl) hmsub
      (by rw [hmdst, hσi, hR.2.2.2.2.2.2.1, hmprev, hidxZ]; omega) hlok
    rw [this]; rfl
  · rw [← heq]; exact oneLess_of_msgs σ _ mabs (by rfl) hnd hcnt

/-- **A rejected append request's effect** (the log not matching; pre-vote and check-quorum off). -/
theorem lineEffect_rejectRecv (C : List w64) (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg)
    (a : Etcdraft.Server) (mabs : Etcdraft.Msg) (Mid : Etcdraft.Server → Prop) (hty : m.ty = .app)
    (hev : SendEvOf (W64 10) m.dst s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : m.dst ∈ C) (hR : SimServerR C C.length (toPState s) a) (hs : LogShapeOk C.length (toPState s))
    (hrole : s.role = .follower) (hterm : m.term = s.term)
    (hmt0 : ¬ PlogMatches (entryID.mk (W64 0) (W64 0)) (toPState s).log (entryID.mk m.logterm (W64 (uint.nat m.index))))
    (hlt0 : uint.nat m.index = 0 → m.logterm = W64 0)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (bmc : uint.Z m.commit < 2 ^ 63)
    (bi : uint.Z m.index < 2 ^ 63) (blt : uint.Z m.logterm < 2 ^ 63) (bk : m.entries.length < 2 ^ 63)
    (hmabs : msgAbs C C.length m = some mabs) :
    LineEffect C false e (idAbs m.dst) a { a with lead := idAbs m.src } (some mabs) (fun b => b.without mabs)
      (fun b => b.with (rjResp a (idAbs m.dst) (idAbs m.src))) Mid := by
  have hev' := hev
  obtain ⟨hname, hnid, hterm', hvote, hcommit', hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev'
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  obtain ⟨hname', hrn, hrp⟩ := aerLine e s cfg m hname
  have hmt : mabs.type = .appendEntriesRequest := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmterm : mabs.term = uint.Z m.term := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hidxZ : ((uint.nat m.index : Nat) : Int) = uint.Z m.index := by word
  have hmprev : mabs.prevLogIndex = (uint.nat m.index : Nat) := by
    rw [hidxZ]; simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmpt : mabs.prevLogTerm = uint.Z m.logterm := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmdst : mabs.dest = idAbs m.dst := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmsrc : mabs.source = idAbs m.src := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hpred : recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) mabs = true := by
    rw [hrp, ← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    have := isAER_app C C.length e m.dst s.vote xs m tm hmsg hm hty (by rw [hterm]; exact bt) bmc bi blt bk
    simp only [hmabs, Option.get_some] at this; exact this
  apply lineEffect_recv1 C false e (idAbs m.dst) a _ mabs _ _ Mid _
    (aerParse e s cfg m tm hname hnid hvote xs hxs hconf hmsg hm (Or.inl hty)) rfl
    (by simp only [msgLine, evConv]; rw [hname']; rfl) hpred hmdst
  intro σ hsrv hσi hpv hcq hnd hcnt
  have hcontains : σ.server.contains (idAbs m.dst) = true := by
    rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  have heq : rejRecvSt σ mabs = withNode σ (idAbs m.dst) { a with lead := idAbs m.src }
      (fun b => b.without mabs) (fun b => b.with (rjResp a (idAbs m.dst) (idAbs m.src))) := by
    unfold rejRecvSt
    rw [hmdst, hmsrc, hσi]
    have := withLead_reply σ (idAbs m.dst) (idAbs m.src) (rjResp a (idAbs m.dst) (idAbs m.src)) mabs
    rw [hσi] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · rw [← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    have hsm := stateMatches_node C s (σ.s (idAbs m.dst)) e m.dst xs (by rw [hσi]; exact hR) hs
      (by rw [hrole]; decide) hterm' hcommit' hrl hlog (hxs.trans hin) bt bc bl σ rfl hcontains
    unfold Etcdraft.Line.stateMatches at hsm ⊢
    simpa [msgLine, nodeLine] using hsm
  · rw [← heq]
    have hlok : LogOkL mabs (σ.s mabs.dest).log = false := by
      rw [hmdst, hσi, hR.2.2.2.2.2.1, logOkL_abs C C.length mabs _ (uint.nat m.index) m.logterm hmprev hmpt
        (fun k x hk hx => hs.2.2 k x (by omega) hx) hlt0 (by word)]
      exact decide_eq_false hmt0
    have := receive_appReject σ mabs (by rw [hmdst]; exact hcontains) hmt
      (by rw [hmdst, hσi, hR.2.1]; simp [toPState, hrole, proleRole]; rfl)
      (by rw [hmdst, hσi, hR.1, hmterm, hterm]; rfl) hpv hcq hlok
    rw [this]; rfl
  · rw [← heq]; exact oneLess_of_msgs σ _ mabs (by rfl) hnd hcnt

/-- **A two-round receive line's effect** (a first round to node `i`'s server `u`, fresh by term or
role, keeping the bags; then one handler round consuming `m`): the intermediate state's shape is
`(· = u)`. -/
theorem lineEffect_recv2 (C : List w64) (e : TraceEv) (i : Etcdraft.ID) (a u a' : Etcdraft.Server)
    (m : Etcdraft.Msg) (fM fP : Etcdraft.Bag → Etcdraft.Bag) (ln : Etcdraft.Line)
    (hparse : Etcdraft.parseLine 0 (evConv e) = .ok ln) (hnid : ln.nid = i)
    (hrecv : Etcdraft.isReceiveName ln.ev.name = true) (hmatch : recvPred ln m = true) (hdest : m.dest = i)
    (hkey : srvKey u ≠ srvKey a)
    (hrcv : ∀ σ : Etcdraft.State, σ.server = confAbs C → σ.s i = a → σ.preVote = false → σ.checkQuorum = false →
      σ.messages.domain.Nodup → 0 < Etcdraft.Bag.count σ.messages m →
      ln.stateMatches σ i = true ∧ σ.receive m = .ok [withNode σ i u _root_.id _root_.id] ∧
      (withNode σ i u _root_.id _root_.id).receive m = .ok [withNode σ i a' fM fP] ∧
      Etcdraft.oneLessMessage (withNode σ i u _root_.id _root_.id) (withNode σ i a' fM fP) m = true) :
    LineEffect C false e i a a' (some m) fM fP (· = u) := by
  refine ⟨ln, hparse, hnid, ?_⟩
  intro t l pl σ hline hl0 hl hb hts _ hsrv hσi hpv hcq hrc hmid hfin
  obtain ⟨hnd, hmem, hcnt, huniq⟩ := hrc
  obtain ⟨hsm, hr1, hr2, hone2⟩ := hrcv σ hsrv hσi hpv hcq hnd hcnt
  have hU : (withNode σ i u _root_.id _root_.id).messages = σ.messages := rfl
  have hUi : (withNode σ i u _root_.id _root_.id).s i = u := by simp [withNode]
  have hone1 : Etcdraft.oneLessMessage σ (withNode σ i u _root_.id _root_.id) m = false := by
    unfold Etcdraft.oneLessMessage; rw [hU]; simp; intro h; rw [h]; decide
  have hdi : i ∈ σ.server := by
    rw [← hdest]
    by_cases h : σ.server.contains m.dest = true
    · exact List.contains_iff_mem.1 h
    · exfalso
      have h' : σ.server.contains m.dest = false := by simpa using h
      unfold Etcdraft.State.receive at hr1
      simp only [h', Bool.not_false, ↓reduceIte, pure, Except.pure] at hr1
      cases hr1
  refine ⟨⟨withNode σ i a' fM fP, l + 1, l⟩, rfl, ?_⟩
  apply Chain.step _ _ ⟨withNode σ i u _root_.id _root_.id, l, l⟩ _ _ rfl
    (memEq_false_of_logs_or_term _ _ i (by
      intro v hv; simp only [List.mem_singleton] at hv; subst hv
      exact ⟨hdi, Or.inr (by simp only; rw [hσi, hUi]; exact fun h => hkey h.symm)⟩)) (hmid u rfl)
  · refine Chain.last _ ⟨withNode σ i u _root_.id _root_.id, l, l⟩ ⟨withNode σ i a' fM fP, l + 1, l⟩ ?_ rfl hfin
    have := next_receive t ⟨withNode σ i u _root_.id _root_.id, l, l⟩ m _ hl0 hl hb (by rw [hline]; exact hrecv)
      (by rw [hU]; exact hnd) (by rw [hU]; exact hmem) (by rw [hline]; exact hmatch)
      (validatePre_later _ _ hl0 _ _)
      (fun m' hm' hne => by rw [hU] at hm'; rw [hline]; simp [huniq m' hm' hne]) hr2
    rw [this]; simp [recvNext, hone2]
  · have := next_receive t ⟨σ, l, pl⟩ m _ hl0 hl hb (by rw [hline]; exact hrecv) hnd hmem
      (by rw [hline]; exact hmatch)
      (by unfold Etcdraft.Trace.validatePreStates; rw [hline, hdest, hsm]; simp)
      (fun m' hm' hne => by rw [hline]; simp [huniq m' hm' hne]) hr1
    rw [this]; simp [recvNext, hone1]

theorem truncSt_eq (σ : Etcdraft.State) (i j : Etcdraft.ID) (L : List Etcdraft.Entry) :
    truncSt σ i j L = withNode σ i { σ.s i with log := L, lead := j } _root_.id _root_.id := by
  unfold truncSt withLead withNode Etcdraft.State.upd
  simp only
  congr 1
  funext k; by_cases hk : k = i <;> simp [hk]

/-- The accepted append request's last state's server. -/
def doneSrv (a : Etcdraft.Server) (L : List Etcdraft.Entry) (j : Etcdraft.ID) (c : Int) : Etcdraft.Server :=
  { a with log := L, lead := j, commitIndex := max a.commitIndex c }

/-- The accepted append request's response. -/
def doneResp (a : Etcdraft.Server) (m : Etcdraft.Msg) (p k : Nat) : Etcdraft.Msg :=
  { type := .appendEntriesResponse, subtype := m.subtype, term := a.currentTerm, success := true, matchIndex := (p : Int) + k, source := m.dest, dest := m.source }

theorem withNode_withNode (σ : Etcdraft.State) (i : Etcdraft.ID) (v w : Etcdraft.Server)
    (fM fP : Etcdraft.Bag → Etcdraft.Bag) :
    withNode (withNode σ i v _root_.id _root_.id) i w fM fP = withNode σ i w fM fP := by
  unfold withNode
  simp only
  congr 1
  funext k; by_cases hk : k = i <;> simp [hk]

theorem withNode_s_self (σ : Etcdraft.State) (i : Etcdraft.ID) (v : Etcdraft.Server) (fM fP : Etcdraft.Bag → Etcdraft.Bag) :
    (withNode σ i v fM fP).s i = v := by simp [withNode]

theorem doneSt_truncSt_eq (σ : Etcdraft.State) (m : Etcdraft.Msg) (L : List Etcdraft.Entry) (p k : Nat) :
    doneSt (truncSt σ m.dest m.source L) m p k =
      withNode σ m.dest (doneSrv (σ.s m.dest) L m.source (min m.commitIndex ((p : Int) + k)))
        (fun b => b.without m) (fun b => b.with (doneResp (σ.s m.dest) m p k)) := by
  unfold doneSt Etcdraft.State.commitTo
  rw [withLead_reply_upd, truncSt_eq, withNode_s_self, withNode_withNode]
  rfl

/-- **The `Ready` line's step, any run** (`simRun_ready` without `L ≠ []`). -/
theorem simRun_ready_any (C : List w64) (L : List TraceEv) (σ : Etcdraft.State) (hrun : SimRun C L σ)
    (hσinv : σ.violated = .ok none) (e : TraceEv) (id : w64) (s : NState) (cfg : CfgM)
    (hev : NodeEvOf (W64 8) id s cfg e) (hout : cfg.outgoing = ∅) (hC : id ∈ C)
    (hinv : (σ.ready (idAbs id)).violated = .ok none) :
    SimRun C (L ++ [e]) (σ.ready (idAbs id)) := by
  obtain ⟨hname, hnid, -, hvote, -, -, -, ⟨xs, ys, -, hys, hconf⟩, hmsg, -, -, -, -⟩ := hev
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  have hname' : gsStr e.name = "Ready" := by
    simp only [evtNames] at hname
    have : e.name = go!"Ready" := by have := hname; simp at this; exact this.symm
    rw [this]; rfl
  have hparse : Etcdraft.parseLine L.length (evConv e) = .ok (nodeLine e id s.vote xs) :=
    parseLine_node L.length e id s.vote xs [] hnid hvote hconf hmsg (by rw [hname']; rfl) (by rw [hname']; decide)
  apply simRun_snoc_single_any C L σ _ e _ hrun hσinv hparse _ hinv
  intro lines ts hl hts hl'
  have hlen := parseLines_length _ _ hl
  simp only [List.length_map] at hlen
  have hline := linesTrace_line_last C lines (nodeLine e id s.vote xs) ts.l (by omega)
  apply next_of_nonReceive _ ts _ (by omega) (by simp [linesTrace, Etcdraft.Trace.len]; omega)
  · simp only [linesTrace]; rw [hl']
    have := bootFlags_nonBoot (confAbs C) lines (nodeLine e id s.vote xs) (by simp [nodeLine, evConv, hname']; rfl)
    rw [hlen] at this; exact this
  · rw [hline]; simp [nodeLine, evConv, hname']; rfl
  · rw [← hts]
    apply nonReceive_ready _ ts (idAbs id) (by simp [linesTrace, Etcdraft.Trace.len]; omega)
    · rw [hline]; simp [nodeLine, evConv, hname']
    · rw [hline]; rfl
    · exact confAbs_nodup C
    · simp only [linesTrace]; rw [mem_confAbs]; exact hC

/-- **A server the application's `ApplyConfChange` leaves as it is** (`ApplySimpleConfChange`): not
joint, its commit index within its log, not a leader, the last configuration entry it has committed
(`k`, the specification's `SelectLastInSubSeq`) its configuration, and no progress outside it. -/
def AccIdle (a : Etcdraft.Server) : Prop :=
  a.config.outgoing.isEmpty = true ∧ a.commitIndex ≤ a.log.length ∧ a.state ≠ Etcdraft.leader ∧
  ∃ (k : Nat) (nc lr : Etcdraft.SetIds),
    (List.range a.commitIndex.toNat).foldl
      (fun (acc : Nat) n => if ((a.log[n]?).map Etcdraft.Entry.type) == some .config then n + 1 else acc) 0 = k ∧
    0 < k ∧ (k : Int) ≤ a.commitIndex ∧ (a.log[k - 1]?).map Etcdraft.Entry.value = some (.conf nc lr) ∧
    a.config = Etcdraft.Config.mk nc [] lr ∧
    ∀ j, (nc.union lr).contains j = false → a.matchIndex j = 0

theorem applySimpleConfChange_idle (σ : Etcdraft.State) (i : Etcdraft.ID) (h : AccIdle (σ.s i)) :
    σ.applySimpleConfChange i = .ok (some σ) := by
  obtain ⟨hj, hci, hnl, k, nc, lr, hk, hk0, hkc, hkv, hcfg, hmi⟩ := h
  unfold Etcdraft.State.applySimpleConfChange Etcdraft.State.isJointConfig
  simp only [hj, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [hk]
  have hnot : ¬ ((σ.s i).commitIndex > ((σ.s i).log.length : Int)) := by omega
  have hnl' : ((σ.s i).state == Etcdraft.leader) = false := by simpa using hnl
  simp only [hnot, ↓reduceIte, hk0, hkc, decide_true, Bool.true_and, Bool.not_true, hnl', Bool.false_and,
    hkv, Bool.false_eq_true]
  simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq]
  have hupd : ∀ (τ : Etcdraft.State) (f : Etcdraft.Server → Etcdraft.Server), f (τ.s i) = τ.s i → τ.upd i f = τ := by
    intro τ f hf
    unfold Etcdraft.State.upd
    have : (fun j => if j = i then f (τ.s i) else τ.s j) = τ.s := by
      funext j; by_cases hji : j = i
      · subst hji; simp [hf]
      · simp [hji]
    rw [this]
  have happ : σ.applyConfigUpdate i k = σ := by
    unfold Etcdraft.State.applyConfigUpdate
    simp only [hkv]
    apply hupd
    rw [← hcfg]
  rw [happ]
  apply hupd
  generalize σ.s i = v at hmi
  cases v with
  | mk ct st vf ld lg ci vr vg mi pc cf du =>
    simp only [Etcdraft.Server.mk.injEq, true_and, and_true]
    funext x
    by_cases hx : (nc.union lr).contains x = true
    · simp only [hx, ↓reduceIte]
    · simp only [hx, Bool.false_eq_true, ↓reduceIte]; exact (hmi x (by simpa using hx)).symm


/-- An `ApplyConfChange` line's non-receive successor, at a server it leaves as it is: the state. -/
theorem nonReceive_applyCC (t : Etcdraft.Trace) (ts : Etcdraft.TState) (i : Etcdraft.ID) (hl : ts.l ≤ t.len)
    (hname : (t.line ts.l).ev.name = "ApplyConfChange") (hnid : (t.line ts.l).nid = i)
    (hnd : t.server.Nodup) (hi : i ∈ t.server) (hacc : AccIdle (ts.s.s i)) :
    t.nonReceive ts = .ok [ts.s] := by
  have hf : t.server.foldlM (fun acc j => do return acc ++ (← t.applySimpleConfChangeIfLogged ts j)) [] =
      .ok [ts.s] := by
    apply foldlM_append_single _ _ i _ hnd hi
    · simp [Etcdraft.Trace.applySimpleConfChangeIfLogged, Etcdraft.Trace.isNodeEvent, Etcdraft.Trace.isEvent,
        hl, hname, hnid, applySimpleConfChange_idle _ _ hacc, Etcdraft.somes, bind, Except.bind, pure, Except.pure]
    · intro j _ hj
      simp [Etcdraft.Trace.applySimpleConfChangeIfLogged, Etcdraft.Trace.isNodeEvent, Etcdraft.Trace.isEvent,
        hnid, Ne.symm hj, pure, Except.pure]
  unfold Etcdraft.Trace.nonReceive
  simp only [hname, hf]
  simp [Etcdraft.Trace.skipUnusedLogline, Etcdraft.Trace.isEvent, hname,
    Etcdraft.Trace.isBecomeFollowerInUpdateTermOrReturnToFollower, pure, Except.pure, bind, Except.bind]

/-- **The application's `ApplyConfChange` line's effect** (past the node's segment): none, at a
server it leaves as it is (`AccIdle`). -/
theorem lineEffect_applyCC (C : List w64) (e : TraceEv) (id vote : w64) (xs : List w64)
    (a : Etcdraft.Server) (Mid : Etcdraft.Server → Prop)
    (hnid : e.nid = decStr id) (hvote : e.vote = decStr vote)
    (hconf : e.conf = (xs.map decStr, ([] : List w64).map decStr)) (hmsg : e.msg = none)
    (hname : gsStr e.name = "ApplyConfChange") (hC : id ∈ C) (hacc : AccIdle a) :
    LineEffect C false e (idAbs id) a a none _root_.id _root_.id Mid := by
  apply lineEffect_nr C false e (idAbs id) a a _root_.id Mid (nodeLine e id vote xs)
    (parseLine_node 0 e id vote xs [] hnid hvote hconf hmsg (by rw [hname]; rfl) (by rw [hname]; decide)) rfl
    (by simp [nodeLine, evConv, hname]; rfl)
  intro t l pl σ hline hl hts _ hsrv hσi _ _
  have hF : withNode σ (idAbs id) a _root_.id _root_.id = σ := by rw [← hσi, withNode_same]; rfl
  rw [hF]
  apply nonReceive_applyCC _ _ (idAbs id) hl
  · rw [hline]; simp [nodeLine, evConv, hname]
  · rw [hline]; rfl
  · rw [hts]; exact confAbs_nodup C
  · rw [hts, mem_confAbs]; exact hC
  · rw [hσi]; exact hacc


/-- The accepted append request's intermediate servers: the log truncated to `k` entries
(`p ≤ k`), or the new log, the leader adopted. -/
def appMid (C : List w64) (a : Etcdraft.Server) (src : Etcdraft.ID) (log es' : List EntryM) (p : Nat)
    (v : Etcdraft.Server) : Prop :=
  (∃ k, p ≤ k ∧ k < log.length ∧ v = { a with log := logAbs C C.length 1 (log.take k), lead := src }) ∨
  v = { a with log := logAbs C C.length 1 es', lead := src }

/-- **An accepted append request's effect** (at a follower of its term, raft's `maybeAppend`
succeeding: the rule `appAccept`): the truncations and the append (`appMid`), then
`AppendEntriesAlreadyDone`, the request consumed and the response pending. -/
theorem lineEffect_appRecv (C : List w64) (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg)
    (a : Etcdraft.Server) (mabs : Etcdraft.Msg) (hty : m.ty = .app)
    (hev : SendEvOf (W64 10) m.dst s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : m.dst ∈ C) (hR : SimServerR C C.length (toPState s) a) (hs : LogShapeOk C.length (toPState s))
    (hrole : s.role = .follower) (hterm : m.term = s.term)
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
    (hmabs : msgAbs C C.length m = some mabs) :
    LineEffect C false e (idAbs m.dst)
      a (doneSrv a (logAbs C C.length 1 es') (idAbs m.src)
          (min mabs.commitIndex ((uint.nat m.index : Int) + m.entries.length)))
      (some mabs) (fun b => b.without mabs)
      (fun b => b.with (doneResp a mabs (uint.nat m.index) m.entries.length))
      (appMid C a (idAbs m.src) (toPState s).log es' (uint.nat m.index)) := by
  have hev' := hev
  obtain ⟨hname, hnid, hterm', hvote, hcommit', hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev'
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  obtain ⟨hname', hrn, hrp⟩ := aerLine e s cfg m hname
  have hidxZ : ((uint.nat m.index : Nat) : Int) = uint.Z m.index := by word
  have hmt : mabs.type = .appendEntriesRequest := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmsub : mabs.subtype = "app" := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmterm : mabs.term = uint.Z m.term := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmprev : mabs.prevLogIndex = (uint.nat m.index : Nat) := by
    simp [msgAbs, hty] at hmabs; rw [← hmabs, hidxZ]
  have hmpt : mabs.prevLogTerm = uint.Z m.logterm := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hments : mabs.entries = logAbs C C.length (uint.nat m.index + 1) m.entries := by
    simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmdst : mabs.dest = idAbs m.dst := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hmsrc : mabs.source = idAbs m.src := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
  have hpred : recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) mabs = true := by
    rw [hrp, ← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    have := isAER_app C C.length e m.dst s.vote xs m tm hmsg hm hty (by rw [hterm]; exact bt) bmc bi blt bk
    simp only [hmabs, Option.get_some] at this
    exact this
  refine ⟨msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming),
    aerParse e s cfg m tm hname hnid hvote xs hxs hconf hmsg hm (Or.inl hty), rfl, ?_⟩
  intro t l pl σ hline hl0 hl hb hts _ hsrv hσi hpv hcq hrc hmids hfin
  obtain ⟨hnd, hmem, hcnt, huniq⟩ := hrc
  have hcontains : σ.server.contains (idAbs m.dst) = true := by
    rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  have hσR : SimServerR C C.length (toPState s) (σ.s (idAbs m.dst)) := by rw [hσi]; exact hR
  have hsm : (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)).stateMatches σ (idAbs m.dst) = true := by
    rw [← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    have := stateMatches_node C s (σ.s (idAbs m.dst)) e m.dst xs hσR hs (by rw [hrole]; decide) hterm' hcommit' hrl
      hlog (hxs.trans hin) bt bc bl σ rfl hcontains
    unfold Etcdraft.Line.stateMatches at this ⊢
    simpa [msgLine, nodeLine] using this
  have hdone := doneSt_truncSt_eq σ mabs (logAbs C C.length 1 es') (uint.nat m.index) m.entries.length
  rw [hmdst, hmsrc, hσi] at hdone
  refine ⟨⟨doneSt (truncSt σ mabs.dest mabs.source (logAbs C C.length 1 es')) mabs (uint.nat m.index)
    m.entries.length, l + 1, l⟩, by rw [hmdst, hmsrc, hdone], ?_⟩
  have hT : ∀ L : List Etcdraft.Entry, truncSt σ mabs.dest mabs.source L =
      withNode σ (idAbs m.dst) { a with log := L, lead := idAbs m.src } _root_.id _root_.id := by
    intro L; rw [truncSt_eq, hmdst, hmsrc, hσi]
  apply chain_appAccept t l pl σ mabs C C.length (uint.nat m.index) m.logterm lastnewi (toPState s).log m.entries es' []
    (by simp) hl0 hl hb (by rw [hline]; simp [msgLine, evConv, hname']; rfl) hnd hmem hcnt (by rw [hline]; exact hpred)
    (by unfold Etcdraft.Trace.validatePreStates; rw [hline, hmdst, hsm]; simp)
    (by rw [hline]; exact huniq) (by rw [hmdst]; exact hcontains) hmt
    (by rw [hmdst, hσR.2.1]; simp [toPState, hrole, proleRole]; rfl)
    (by rw [hmdst, hσR.1, hmterm, hterm]; rfl) hmsub (by rw [hmdst]; exact hσR.2.2.2.2.2.1)
    hments hmprev hmpt (fun h => hlt0 h)
    (by rw [hmdst, hσR.2.2.2.2.2.2.1, hidxZ]; omega) (fun k x hk hx => hs.2.2 k x (by omega) hx) hbe hwf (by word) hnw happ
  · intro k hk1 hk2
    rw [hT]; exact hmids _ (Or.inl ⟨k, hk1, hk2, rfl⟩)
  · rw [hT]; exact hmids _ (Or.inr rfl)
  · rw [hmdst, hmsrc, hdone]; exact hfin


/-- **A lower-term response's effect** (raft ignores it; the specification drops it). -/
theorem lineEffect_staleResp (C : List w64) (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg) (evt : w64)
    (a : Etcdraft.Server) (mabs : Etcdraft.Msg) (Mid : Etcdraft.Server → Prop)
    (htyev : (m.ty = .appResp ∧ evt = W64 12) ∨ (m.ty = .voteResp ∧ evt = W64 16))
    (hev : SendEvOf evt m.dst s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : m.dst ∈ C) (hR : SimServerR C C.length (toPState s) a) (hs : LogShapeOk C.length (toPState s))
    (hpre : s.role ≠ .preCandidate) (hlt : uint.Z m.term < uint.Z s.term)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (bi : uint.Z m.index < 2 ^ 63)
    (hmabs : msgAbs C C.length m = some mabs) :
    LineEffect C false e (idAbs m.dst) a a (some mabs) (fun b => b.without mabs) _root_.id Mid := by
  have hev' := hev
  obtain ⟨hname, hnid, hterm', hvote, hcommit', hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev'
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  obtain ⟨nm, hname', hrn, htyp, hmt, hmdst, hmterm, hpred⟩ :=
    respLine C e s cfg m evt htyev hname tm hmsg hm (by omega) bi mabs hmabs
  have hparse : Etcdraft.parseLine 0 (evConv e) = .ok (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) := by
    rw [← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    exact parseLine_msg 0 e m.dst s.vote m.src m.dst xs [] tm hnid hvote hconf hmsg hm.2.2.1 hm.2.2.2.1
      (by rw [hm.1]; exact htyp)
      (by rw [hname']; intro h; rw [h] at hrn; exact absurd hrn (by decide))
  apply lineEffect_recv1 C false e (idAbs m.dst) a _ mabs _ _ Mid _ hparse rfl
    (by simp only [msgLine, evConv]; rw [hname']; exact hrn) hpred hmdst
  intro σ hsrv hσi _ _ hnd hcnt
  have hcontains : σ.server.contains (idAbs m.dst) = true := by
    rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  have heq : σ.discard mabs = withNode σ (idAbs m.dst) a (fun b => b.without mabs) _root_.id := by
    unfold withNode Etcdraft.State.discard
    have : (fun j => if j = idAbs m.dst then a else σ.s j) = σ.s := by
      funext j; split <;> simp_all
    rw [this]; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    have hsm := stateMatches_node C s (σ.s (idAbs m.dst)) e m.dst xs (by rw [hσi]; exact hR) hs hpre hterm'
      hcommit' hrl hlog (hxs.trans hin) bt bc bl σ rfl hcontains
    unfold Etcdraft.Line.stateMatches at hsm ⊢
    simpa [msgLine, nodeLine] using hsm
  · rw [← heq]
    exact receive_staleResp σ mabs (by rw [hmdst]; exact hcontains) hmt.symm
      (by rw [hmdst, hσi, hR.1, hmterm]; exact hlt)
  · rw [← heq]; exact oneLess_of_msgs σ _ mabs (by rfl) hnd hcnt

/-- The phantom reply to a lower-term request, at its receiver's server `a`. -/
def phantomOf (a : Etcdraft.Server) (mabs : Etcdraft.Msg) : Etcdraft.Msg :=
  if mabs.type = .requestVoteRequest then
    { type := .requestVoteResponse, term := a.currentTerm, voteGranted := false, source := mabs.dest, dest := mabs.source }
  else
    { type := .appendEntriesResponse, subtype := "app", term := a.currentTerm, success := false, matchIndex := 0, source := mabs.dest, dest := mabs.source }

/-- **A lower-term request's effect** (raft ignores it, pre-vote and check-quorum off; the
specification answers it with a phantom reply, `phantomOf`). -/
theorem lineEffect_staleReq (C : List w64) (e : TraceEv) (s : NState) (cfg : CfgM) (m : Msg) (evt : w64)
    (a : Etcdraft.Server) (mabs : Etcdraft.Msg) (Mid : Etcdraft.Server → Prop)
    (htyev : (m.ty = .app ∧ evt = W64 10) ∨ (m.ty = .vote ∧ evt = W64 14))
    (hev : SendEvOf evt m.dst s cfg m e) (hin : (elements cfg.incoming).Perm C) (hout : cfg.outgoing = ∅)
    (hC : m.dst ∈ C) (hR : SimServerR C C.length (toPState s) a) (hs : LogShapeOk C.length (toPState s))
    (hpre : s.role ≠ .preCandidate) (hlt : uint.Z m.term < uint.Z s.term)
    (bt : uint.Z s.term < 2 ^ 63) (bc : uint.Z s.logst.committed < 2 ^ 63)
    (bl : uint.Z (plastIndex (toPState s)) < 2 ^ 63) (bi : uint.Z m.index < 2 ^ 63)
    (blt : uint.Z m.logterm < 2 ^ 63) (bk : m.entries.length < 2 ^ 63) (bmc : uint.Z m.commit < 2 ^ 63)
    (hmabs : msgAbs C C.length m = some mabs) :
    LineEffect C false e (idAbs m.dst) a a (some mabs) (fun b => b.without mabs)
      (fun b => b.with (phantomOf a mabs)) Mid := by
  have hev' := hev
  obtain ⟨hname, hnid, hterm', hvote, hcommit', hrl, hlog, ⟨xs, ys, hxs, hys, hconf⟩, ⟨tm, hmsg, hm⟩, -⟩ := hev'
  rw [hout, elements_empty_nil] at hys
  have hys0 := List.Perm.eq_nil hys
  subst hys0
  have hnames := recvName_of evt e hname
  have hmdst : mabs.dest = idAbs m.dst := by
    rcases htyev with ⟨hty, -⟩ | ⟨hty, -⟩ <;> (simp [msgAbs, hty] at hmabs; rw [← hmabs])
  have hmterm : mabs.term = uint.Z m.term := by
    rcases htyev with ⟨hty, -⟩ | ⟨hty, -⟩ <;> (simp [msgAbs, hty] at hmabs; rw [← hmabs])
  -- the line's name, its parse and the request's match, by type
  obtain ⟨nm, hname', hrn, htyp, hpred, hrcv⟩ : ∃ nm, gsStr e.name = nm ∧ Etcdraft.isReceiveName nm = true ∧
      (Etcdraft.raftMsgType (gsStr (msgTypeStr m.ty))).isSome = true ∧
      recvPred (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) mabs = true ∧
      ∀ σ : Etcdraft.State, σ.server.contains mabs.dest = true → mabs.term < (σ.s mabs.dest).currentTerm →
        σ.preVote = false → σ.checkQuorum = false →
        σ.receive mabs = .ok [σ.reply (phantomOf (σ.s mabs.dest) mabs) mabs] := by
    rcases htyev with ⟨hty, rfl⟩ | ⟨hty, rfl⟩
    · have hmt : mabs.type = .appendEntriesRequest := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
      have hname' := hnames.1 rfl
      refine ⟨_, hname', by rfl, by rw [hty]; rfl, ?_, ?_⟩
      · rw [recvPred_aer _ _ (by rw [msgLine_name, hname'])]
        have := isAER_app C C.length e m.dst s.vote (elements cfg.incoming) m tm hmsg hm hty (by omega) bmc bi blt bk
        simp only [hmabs, Option.get_some] at this; exact this
      · intro σ hc hl hpv hcq
        have hph : phantomOf (σ.s mabs.dest) mabs = { type := .appendEntriesResponse, subtype := "app", term := (σ.s mabs.dest).currentTerm, success := false, matchIndex := 0, source := mabs.dest, dest := mabs.source } := by
          unfold phantomOf; simp [hmt]
        rw [hph]; exact receive_staleAER σ mabs hc hmt hl hpv hcq
    · have hmt : mabs.type = .requestVoteRequest := by simp [msgAbs, hty] at hmabs; rw [← hmabs]
      have hname' := hnames.2.2.1 rfl
      refine ⟨_, hname', by rfl, by rw [hty]; rfl, ?_, ?_⟩
      · rw [recvPred_rvreq _ _ (by rw [msgLine_name, hname'])]
        have := isRVReq_vote C C.length e m.dst s.vote (elements cfg.incoming) m tm hmsg hm hty (by omega) bi blt
        simp only [hmabs, Option.get_some] at this; exact this
      · intro σ hc hl _ _
        have hph : phantomOf (σ.s mabs.dest) mabs = { type := .requestVoteResponse, term := (σ.s mabs.dest).currentTerm, voteGranted := false, source := mabs.dest, dest := mabs.source } := by
          unfold phantomOf; simp [hmt]
        rw [hph]; exact receive_staleVoteReq σ mabs hc hmt hl
  have hparse : Etcdraft.parseLine 0 (evConv e) = .ok (msgLine e m.dst s.vote m.src m.dst (elements cfg.incoming)) := by
    rw [← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    exact parseLine_msg 0 e m.dst s.vote m.src m.dst xs [] tm hnid hvote hconf hmsg hm.2.2.1 hm.2.2.2.1
      (by rw [hm.1]; exact htyp)
      (by rw [hname']; intro h; rw [h] at hrn; exact absurd hrn (by decide))
  apply lineEffect_recv1 C false e (idAbs m.dst) a _ mabs _ _ Mid _ hparse rfl
    (by simp only [msgLine, evConv]; rw [hname']; exact hrn) hpred hmdst
  intro σ hsrv hσi hpv hcq hnd hcnt
  have hcontains : σ.server.contains (idAbs m.dst) = true := by
    rw [hsrv, List.contains_iff_mem, mem_confAbs]; exact hC
  have heq : σ.reply (phantomOf (σ.s mabs.dest) mabs) mabs =
      withNode σ (idAbs m.dst) a (fun b => b.without mabs) (fun b => b.with (phantomOf a mabs)) := by
    rw [hmdst, hσi]
    unfold withNode Etcdraft.State.reply
    have : (fun j => if j = idAbs m.dst then a else σ.s j) = σ.s := by
      funext j; split <;> simp_all
    rw [this]
  refine ⟨?_, ?_, ?_⟩
  · rw [← msgLine_perm e m.dst s.vote m.src m.dst xs _ hxs]
    have hsm := stateMatches_node C s (σ.s (idAbs m.dst)) e m.dst xs (by rw [hσi]; exact hR) hs hpre hterm'
      hcommit' hrl hlog (hxs.trans hin) bt bc bl σ rfl hcontains
    unfold Etcdraft.Line.stateMatches at hsm ⊢
    simpa [msgLine, nodeLine] using hsm
  · rw [← heq]
    exact hrcv σ (by rw [hmdst]; exact hcontains) (by rw [hmdst, hσi, hR.1, hmterm]; exact hlt) hpv hcq
  · rw [← heq]; exact oneLess_of_msgs σ _ mabs (by rfl) hnd hcnt

end TraceSim

end EtcdGrove
end Perennial
