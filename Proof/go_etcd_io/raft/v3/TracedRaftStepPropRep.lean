/-
Lean-first (no Rocq counterpart). **`raft.Step`'s traced bundle on `MsgProp` at a leader: the
`Replicate` lines** (2026-11-11, trace-check Q8 stage 1 slice 24a, `notes/decisions.md`, "Q8 stage 1
(slice 24a)").

`appendEntry` logs one `Replicate` line per (normal) entry of the batch, all at the state before the
append (`traceReplicate` runs before `raftLog.append`); the specification's `ClientRequest` appends
one value entry of the leader's term per line. The share's server steps along the states with the
batch's first `k` entries appended (`propK s es k = propAppended s (es.take k)`):

- **the phase step** (`phaseStepB_replicate`): `lineEffect_replicate`, the idle relation at the
  `k + 1`-th state (`simServerR_append`: the abstract log grows by `entAbs` of the stamped entry, a
  value entry of the leader's term past the bootstrap entries; `LogShapeOk` and the `2^63` bounds);
- **the facts** (`fxPres_replicate`): the specification's `ClientRequest` (`specInv_clientRequest`),
  the leader's server facts with the new entry among its *pending* entries (`srvFacts`' `pend`, review
  finding A9: no record needed, the records being raft's ghost state's, which the family moved to the
  proposed state before the lines), `AppSlices` by `appSlices_extend`, `QuorumLogF` by
  `quorumLogF_grow`.

Past the bootstrap entries: the leader's last entry is of its term (raft's campaign record,
`ownStepGhost_leadLast`) and the bootstrap entries are of term `1` (`LogShapeOk`), so at a term `≥ 2`
the log reaches past them; a leader's term is `≥ 2` in a cluster with a bootstrap log
(`ownStepGhost_leadLast`'s last clause), which the path premises (`PropLead`'s).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepProp
public import Proof.go_etcd_io.raft.v3.TracedQuorumLog

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts]

/-- The state with the batch's first `k` entries appended (`appendEntry`'s state after its `k`-th
`Replicate` line's entry, before the self-acknowledgement). -/
abbrev propK (s : NState) (es : List EntryM) (k : Nat) : NState := propAppended s (es.take k)

theorem logAbs_snoc (C : List w64) (bl first : Nat) (l : List EntryM) (x : EntryM) :
    logAbs C bl first (l ++ [x]) = logAbs C bl first l ++ [entAbs C bl (first + l.length) x] := by
  unfold logAbs
  rw [List.mapIdx_append]
  simp

/-- The `k + 1`-th state is the `k`-th with one stamped entry appended. -/
theorem propK_succ (s : NState) (es : List EntryM) (k : Nat) (e : EntryM) (he : es[k]? = some e) :
    propK s es (k + 1) =
      { propK s es k with logst := logAppend (propK s es k).logst [stamp s.term (logLast s.logst) k e] } := by
  have hk : k < es.length := (List.getElem?_eq_some_iff.1 he).1
  have ht : es.take (k + 1) = es.take k ++ [e] := by
    rw [List.take_add_one, he]; rfl
  simp only [propK, propAppended, ht, List.mapIdx_append, logAppend, List.append_assoc]
  simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]

theorem propK_term (s : NState) (es : List EntryM) (k : Nat) : (propK s es k).term = s.term := rfl
theorem propK_role (s : NState) (es : List EntryM) (k : Nat) : (propK s es k).role = s.role := rfl
theorem propK_prvals (s : NState) (es : List EntryM) (k : Nat) : (propK s es k).prvals = s.prvals := rfl
theorem propK_committed (s : NState) (es : List EntryM) (k : Nat) :
    (propK s es k).logst.committed = s.logst.committed := rfl
theorem propK_prev (s : NState) (es : List EntryM) (k : Nat) :
    (propK s es k).logst.prev = s.logst.prev := rfl

/-- The `k`-th state's log length. -/
theorem propK_len (s : NState) (es : List EntryM) (k : Nat) :
    (toPState (propK s es k)).log.length = (toPState s).log.length + min k es.length := by
  simp [propK, propAppended, toPState, logAppend, List.length_take]
  omega

/-- The spec's server with one value entry of its term appended (`ClientRequest`'s, `replicate`). -/
def repSrv (a : Etcdraft.Server) : Etcdraft.Server :=
  { a with log := a.log ++ [{ term := a.currentTerm, type := .value, value := .val 0 }] }

theorem toC_repSrv (srv : Etcdraft.SetIds) (a b : Etcdraft.Server) (h : toC srv a = toC srv b) :
    toC srv (repSrv a) = toC srv (repSrv b) := by
  have ht : a.currentTerm = b.currentTerm := congrArg ServerC.currentTerm h
  have hl : a.log = b.log := congrArg ServerC.log h
  simp only [toC, repSrv] at h ⊢
  rw [ht, hl]
  simp only [ServerC.mk.injEq] at h ⊢
  simp only [true_and]
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2⟩

/-- **The idle relation at the state with one more entry of the leader's term** (past the bootstrap
entries): the abstract log grows by the entry's `entAbs`, a value entry of the server's term. -/
theorem simServerR_append (C : List w64) (bl : Nat) (s : NState) (x : EntryM) (a : Etcdraft.Server)
    (h : SimServerR C bl (toPState s) a) (hk : bl ≤ (toPState s).log.length) (hx : x.Term' = s.term) :
    SimServerR C bl (toPState { s with logst := logAppend s.logst [x] }) (repSrv a) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
  refine ⟨h1, h2, h3, h4, h5, ?_, h7, h8, h9, h10, h11⟩
  have hl : (toPState { s with logst := logAppend s.logst [x] }).log = (toPState s).log ++ [x] := by
    simp [toPState, logAppend]
  rw [hl, logAbs_snoc, ← h6]
  have hn : ¬ (1 + (toPState s).log.length ≤ bl) := by omega
  simp only [repSrv, entAbs, if_neg hn, hx, h1]
  rfl

/-- `LogShapeOk` at the state with one more entry, past the bootstrap entries, at the next index. -/
theorem logShapeOk_append (bl : Nat) (s : NState) (x : EntryM) (h : LogShapeOk bl (toPState s))
    (hk : bl ≤ (toPState s).log.length)
    (hx : uint.Z x.Index' = uint.Z s.logst.prev.index' + ((toPState s).log.length + 1 : Nat)) :
    LogShapeOk bl (toPState { s with logst := logAppend s.logst [x] }) := by
  obtain ⟨hb, hwf, hboot⟩ := h
  have hl : (toPState { s with logst := logAppend s.logst [x] }).log = (toPState s).log ++ [x] := by
    simp [toPState, logAppend]
  refine ⟨hb, ?_, ?_⟩
  · rw [hl]
    intro k e he
    rcases Nat.lt_or_ge k (toPState s).log.length with hk' | hk'
    · rw [List.getElem?_append_left hk'] at he
      exact hwf k e he
    · rw [List.getElem?_append_right hk'] at he
      have hk0 : k - (toPState s).log.length = 0 := by
        have := (List.getElem?_eq_some_iff.1 he).1; simp at this; omega
      rw [hk0] at he
      simp at he
      subst he
      have : k = (toPState s).log.length := by
        have := (List.getElem?_eq_some_iff.1 (by rw [List.getElem?_append_right hk', hk0]; rfl :
          ((toPState s).log ++ [x])[k]? = some x)).1
        simp at this; omega
      subst this
      exact hx
  · rw [hl]
    intro k e hkb he
    rw [List.getElem?_append_left (by omega)] at he
    exact hboot k e hkb he

/-- **The log reaches past the bootstrap entries** (of term `1`, `LogShapeOk`) when its last entry is
of a term `≥ 2`. -/
theorem bl_le_of_last (bl : Nat) (l l' : List EntryM) (x : EntryM) (T : w64)
    (hshape : ∀ k e, k < bl → (l ++ l')[k]? = some e → e.Term' = W64 1) (hlast : l.getLast? = some x)
    (hxt : x.Term' = T) (hT : 2 ≤ uint.Z T) : bl < l.length := by
  obtain ⟨l0, hl0⟩ := List.getLast?_eq_some_iff.1 hlast
  have hlen : l.length = l0.length + 1 := by rw [hl0]; simp
  rcases Nat.lt_or_ge l0.length bl with h | h
  · exfalso
    have hk : (l ++ l')[l0.length]? = some x := by
      rw [hl0, List.append_assoc]; simp
    have := hshape l0.length x h hk
    rw [hxt] at this
    subst this
    have : uint.Z (W64 1) = 1 := rfl
    omega
  · omega

/-- `repSrv` on the share's server (`toC`). -/
def repC (cs : ServerC) : ServerC :=
  { cs with log := cs.log ++ [{ term := cs.currentTerm, type := .value, value := .val 0 }] }

theorem toC_repSrv_eq (srv : Etcdraft.SetIds) (a : Etcdraft.Server) : toC srv (repSrv a) = repC (toC srv a) := rfl

/-- The share's server after `k` `Replicate` lines. -/
def repCN (cs0 : ServerC) : Nat → ServerC
  | 0 => cs0
  | k + 1 => repC (repCN cs0 k)

/-- **The `Replicate` lines' pinned phases**: the voters and the list pinned, the server `repCN cs0 k`
after `k` lines, at the idle server of the `k`-th state. -/
abbrev RepPin (s : NState) (es : List EntryM) (o : List Msg) (C0 : List w64) (cs0 : ServerC)
    (P0 : List Etcdraft.Msg) (k : Nat) : List w64 → ServerC → List Etcdraft.Msg → Prop :=
  fun C cs P => C = C0 ∧ cs = repCN cs0 k ∧ P = P0 ∧ PhaseAt (fun C => SimIdleS C (propK s es k)) o C cs P

theorem idAbs_inj {j id : w64} (h : idAbs j = idAbs id) : j = id := by
  unfold idAbs at h; exact BitVec.eq_of_toNat_eq h

end pure

section phase
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

omit [GooseSemantics] [GooseInterp] go_gctx in
/-- The stamped `k`-th entry's index: the next after the `k`-th state's log. -/
theorem stamp_index_propK (s : NState) (es : List EntryM) (k : Nat) (e : EntryM) (hk : k < es.length)
    (hbnd : plogLastIndexZ (toPState s).base (toPState s).log + es.length < 2 ^ 63) :
    uint.Z (stamp s.term (logLast s.logst) k e).Index' =
      uint.Z (propK s es k).logst.prev.index' + ((toPState (propK s es k)).log.length + 1 : Nat) := by
  rw [propK_len, propK_prev]
  have hm : min k es.length = k := Nat.min_eq_left (Nat.le_of_lt hk)
  rw [hm]
  have h0 := uint_Z_nonneg s.logst.prev.index'
  simp only [plogLastIndexZ, toPState, List.length_append] at hbnd
  simp only [stamp, logLast, toPState, List.length_append]
  push_cast
  have hk' : (k : Int) < es.length := by exact_mod_cast hk
  word

omit [GooseSemantics] [GooseInterp] go_gctx in
/-- **The idle relation after a `Replicate` line** (the `k`-th of the batch): from the `k`-th state's
to the `k + 1`-th's, the server `repSrv`'d. The log reaches past the bootstrap entries
(`bl_le_of_last`: its last entry of the leader's term `≥ 2`, `hlast`, `hT2`), the new last index below
`2^63` (`hbnd`). -/
theorem simIdleS_rep (C : List w64) (s : NState) (es : List EntryM) (k : Nat) (e : EntryM)
    (he : es[k]? = some e)
    (hlast : ∃ x, (toPState s).log.getLast? = some x ∧ x.Term' = s.term) (hT2 : 2 ≤ uint.Z s.term)
    (hbnd : plogLastIndexZ (toPState s).base (toPState s).log + es.length < 2 ^ 63)
    (cs : ServerC) (h : SimIdleS C (propK s es k) cs) : SimIdleS C (propK s es (k + 1)) (repC cs) := by
  obtain ⟨a0, ha0, hR0, hs, bt, bc, bl⟩ := h
  have hk : k < es.length := (List.getElem?_eq_some_iff.1 he).1
  obtain ⟨x, hx, hxt⟩ := hlast
  have hlk : (toPState (propK s es k)).log =
      (toPState s).log ++ (es.take k).mapIdx (stamp s.term (logLast s.logst)) := by
    simp [propK, propAppended, toPState, logAppend]
  have hbl0 : C.length ≤ (toPState s).log.length := Nat.le_of_lt <|
    bl_le_of_last C.length (toPState s).log _ x s.term
      (fun j y hj hy => hs.2.2 j y hj (by rw [hlk]; exact hy)) hx hxt hT2
  have hbl : C.length ≤ (toPState (propK s es k)).log.length := by rw [propK_len]; omega
  have hst : (stamp s.term (logLast s.logst) k e).Term' = (propK s es k).term := rfl
  have hR1 := simServerR_append C C.length (propK s es k) _ a0 hR0 hbl hst
  have hs1 := logShapeOk_append C.length (propK s es k) _ hs hbl (stamp_index_propK s es k e hk hbnd)
  rw [← propK_succ s es k e he] at hR1 hs1
  refine ⟨repSrv a0, by rw [toC_repSrv_eq, ha0], hR1, hs1, bt, bc, ?_⟩
  have hb0 : uint.Z s.logst.prev.index' = 0 := by
    have := hs.1; simp only [toPState, propK, propAppended, logAppend] at this; rw [this]; rfl
  simp only [plastIndex, plogLastIndexZ]
  rw [propK_len]
  simp only [toPState, propK, propAppended, logAppend] at hbnd ⊢
  simp only [plogLastIndexZ] at hbnd
  have hmin : min (k + 1) es.length ≤ es.length := Nat.min_le_right _ _
  rw [hb0] at hbnd ⊢
  have hL' : ((s.logst.sents ++ s.logst.uents).length : Int) + es.length < 2 ^ 63 := by omega
  generalize min (k + 1) es.length = n at hmin ⊢
  generalize (s.logst.sents ++ s.logst.uents).length = L at hL' ⊢
  have : ((L + n : Nat) : Int) < 2 ^ 63 := by push_cast; omega
  word

omit [GooseSemantics] [GooseInterp] go_gctx in
/-- A server the `k`-th state's idle relation admits is a leader's. -/
theorem simIdleS_leader {C : List w64} {s : NState} {es : List EntryM} {k : Nat} {a : Etcdraft.Server}
    (hlead : s.role = .leader) (h : SimIdleS C (propK s es k) (toC (confAbs C) a)) :
    a.state = Etcdraft.leader := by
  obtain ⟨a0, ha0, hR0, -⟩ := h
  have hs : a0.state = a.state := congrArg ServerC.state ha0
  rw [← hs, hR0.2.1]
  simp [toPState, propK, propAppended, hlead, proleRole, roleAbs]

/-- **A `Replicate` line's phase step, pinned** (the `k`-th of the batch `es`, at a leader's state `s`):
`lineEffect_replicate` (`ClientRequest`, a value entry of the leader's term appended), from the pinned
phase after `k` lines to the one after `k + 1` (`simIdleS_rep`), the list kept. -/
theorem phaseStepB_replicate (id : w64) (c : CfgM) (s : NState) (es : List EntryM) (o : List Msg)
    (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg)
    (k : Nat) (e : EntryM) (he : es[k]? = some e) (hlead : s.role = .leader)
    (hlast : ∃ x, (toPState s).log.getLast? = some x ∧ x.Term' = s.term) (hT2 : 2 ≤ uint.Z s.term)
    (hbnd : plogLastIndexZ (toPState s).base (toPState s).log + es.length < 2 ^ 63) :
    PhaseStepB id c (NodeEvOf (W64 5) id s c) (RepPin s es o C0 cs0 P0 k) (RepPin s es o C0 cs0 P0 (k + 1)) := by
  rintro C cs P ⟨rfl, rfl, rfl, hI, hP⟩ ⟨-, hout, hC⟩ ev hev
  refine ⟨hev.2.1, isBootstrapName_bf _ (nodeEvOf_notBoot hev (by decide) (by decide) (by decide)), ?_⟩
  intro a ha
  have hst : a.state = Etcdraft.leader := simIdleS_leader hlead (by rw [ha]; exact hI)
  have hI1 := simIdleS_rep C s es k e he hlast hT2 hbnd _ hI
  have hle := lineEffect_replicate C ev id s c a (fun _ => False) hev hout hC hst
  refine ⟨repSrv a, [], ⟨rfl, by rw [toC_repSrv_eq, ha]; rfl, List.append_nil _, by
    rw [toC_repSrv_eq, ha]; exact hI1, by rw [List.append_nil]; exact hP⟩, fun _ h => (by cases h), hle⟩

end phase

section facts
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

omit [GooseSemantics] [GooseInterp] go_gctx [StorageModel GF] sem package_sem in
/-- A log whose abstract last entry is of the server's term, past the bootstrap entries: its last
entry is of that term. -/
theorem last_term_of_abs (C : List w64) (es : List EntryM) (T : Int)
    (hbl : C.length < es.length) (hT : 0 ≤ T ∧ T < 2 ^ 63)
    (hlast : (logAbs C C.length 1 es).getLast?.map Etcdraft.Entry.term = some T) :
    es.getLast?.map EntryM.Term' = some (W64 T) := by
  cases hl : es.getLast? with
  | none => rw [List.getLast?_eq_none_iff] at hl; subst hl; simp at hbl
  | some y =>
    obtain ⟨es0, rfl⟩ := List.getLast?_eq_some_iff.1 hl
    rw [logAbs_snoc] at hlast
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.map_some] at hlast
    have hn : ¬ (1 + es0.length ≤ C.length) := by simp at hbl; omega
    simp only [entAbs, if_neg hn, Option.some.injEq] at hlast
    simp only [Option.map_some, Option.some.injEq]
    rw [← hlast]
    word

/-- **A leader's facts after its `Replicate` line**: the new entry among its pending entries (`pend`,
review finding A9: raft appends it after the hook; no record needed here), a value entry of its term
past the bootstrap entries; with no pending entry before, the campaign record's clause from its full
log's (`leadFull_camp`, `isLeader_unique`) and its last entry of its term (`hlast`, from raft's log). -/
theorem srvFacts_rep (γ : RaftNames) (C : List w64) (j : w64) (a : Etcdraft.Server)
    (hl : a.state = Etcdraft.leader) (hbl : C.length < a.log.length)
    (hlast : a.log.getLast?.map Etcdraft.Entry.term = some a.currentTerm) (hlen : a.log.length + 1 < 2 ^ 63) :
    srvFacts (GF := GF) γ C j a ⊢ srvFacts γ C j (repSrv a) := by
  have hst : (repSrv a).state = a.state := rfl
  have htm : (repSrv a).currentTerm = a.currentTerm := rfl
  have hcm : (repSrv a).commitIndex = a.commitIndex := rfl
  unfold srvFacts
  rw [hst, htm, hcm]
  simp only [if_pos hl]
  iintro #H
  icases H with ⟨%es, %pend, %Hp, #Hr, #Hc, ⟨#Hil, #Hlf, Hcamp⟩, #Hci⟩
  obtain ⟨hlog, hbt, hwf, hln, hc0, hce, ht0, ht63, hnl, hpt⟩ := Hp
  have hlen' : (es ++ pend).length = a.log.length := by rw [hlog, logAbs_length]
  let x : EntryM := { (zero_val EntryM) with Term' := W64 a.currentTerm, Index' := W64 ((es ++ pend).length + 1 : Nat) }
  iexists es, pend ++ [x]
  isplitr
  · ipureintro
    have hn : ¬ (1 + (es ++ pend).length ≤ C.length) := by omega
    refine ⟨?_, ?_, ?_, ?_, hc0, hce, ht0, ht63, fun h => absurd hl h, ?_⟩
    · show a.log ++ _ = _
      rw [← List.append_assoc, logAbs_snoc, ← hlog]
      have hw : uint.Z (W64 a.currentTerm : w64) = a.currentTerm := by word
      simp only [entAbs, if_neg hn, x, hw]
    · intro k e hk he
      rw [← List.append_assoc] at he
      rcases Nat.lt_or_ge k (es ++ pend).length with hk' | hk'
      · rw [List.getElem?_append_left hk'] at he; exact hbt k e hk he
      · omega
    · intro k e he hk64
      rw [← List.append_assoc] at he
      rcases Nat.lt_or_ge k (es ++ pend).length with hk' | hk'
      · rw [List.getElem?_append_left hk'] at he; exact hwf k e he hk64
      · rw [List.getElem?_append_right hk'] at he
        have hk0 : k - (es ++ pend).length = 0 := by
          have := (List.getElem?_eq_some_iff.1 he).1
          simp only [List.length_singleton] at this; omega
        rw [hk0] at he
        simp only [List.getElem?_cons_zero, Option.some.injEq] at he
        subst he
        have hk1 : k = (es ++ pend).length := by omega
        subst hk1
        simp only [x]
        have : uint.Z (entryID.mk (W64 0) (W64 0)).index' = 0 := rfl
        rw [this] at hk64 ⊢
        word
    · rw [← List.append_assoc, List.length_append]; simp only [List.length_singleton]; omega
    · intro e he
      rcases List.mem_append.1 he with he | he
      · exact hpt e he
      · rw [List.mem_singleton] at he; subst he; rfl
  iframe Hr Hc Hil Hlf Hci
  iright
  icases Hcamp with (%Hp0 | Hx)
  · subst Hp0
    icases leadFull_camp γ (W64 a.currentTerm) es $$ Hlf with ⟨%ldr, %F0, #Hl2, #Hc2, %Hpre⟩
    icases isLeader_unique γ j ldr (W64 a.currentTerm) $$ Hil Hl2 with %Heq
    subst Heq
    iexists F0
    iframe Hc2
    ipureintro
    refine ⟨Hpre, .inr ?_⟩
    rw [List.append_nil] at hlog
    rw [hlog] at hbl hlast
    rw [logAbs_length] at hbl
    exact last_term_of_abs C es a.currentTerm hbl ⟨ht0, ht63⟩ hlast
  · iexact Hx

omit [GooseSemantics] [GooseInterp] go_gctx [StorageModel GF] sem package_sem in
/-- The `k`-th state's log ends in an entry of the leader's term. -/
theorem propK_last (s : NState) (es : List EntryM) (k : Nat)
    (hlast : ∃ x, (toPState s).log.getLast? = some x ∧ x.Term' = s.term) :
    ∃ y, (toPState (propK s es k)).log.getLast? = some y ∧ y.Term' = s.term := by
  have hlk : (toPState (propK s es k)).log =
      (toPState s).log ++ (es.take k).mapIdx (stamp s.term (logLast s.logst)) := by
    simp [propK, propAppended, toPState, logAppend]
  rw [hlk, List.getLast?_append]
  cases hm : ((es.take k).mapIdx (stamp s.term (logLast s.logst))).getLast? with
  | none => simpa using hlast
  | some y =>
    refine ⟨y, by simp, ?_⟩
    have hy := List.mem_of_getLast? hm
    rw [List.mem_mapIdx] at hy
    obtain ⟨i, -, rfl⟩ := hy
    rfl

/-- **What the `Replicate` line's facts read of the share's server at the `k`-th state**: a leader's,
its log past the bootstrap entries ending in an entry of its term, with room for one more. -/
theorem simIdleS_repFacts (C : List w64) (s : NState) (es : List EntryM) (k : Nat) (hk : k < es.length)
    (hlead : s.role = .leader)
    (hlast : ∃ x, (toPState s).log.getLast? = some x ∧ x.Term' = s.term) (hT2 : 2 ≤ uint.Z s.term)
    (hbnd : plogLastIndexZ (toPState s).base (toPState s).log + es.length < 2 ^ 63)
    (a : Etcdraft.Server) (h : SimIdleS C (propK s es k) (toC (confAbs C) a)) :
    a.state = Etcdraft.leader ∧ C.length < a.log.length ∧
      a.log.getLast?.map Etcdraft.Entry.term = some a.currentTerm ∧ a.log.length + 1 < 2 ^ 63 := by
  have hst := simIdleS_leader hlead h
  obtain ⟨a0, ha0, hR0, hs, -⟩ := h
  have hR : SimServerR C C.length (toPState (propK s es k)) a := simServerR_toC ha0 hR0
  obtain ⟨y, hy, hyt⟩ := propK_last s es k hlast
  have hbl : C.length < (toPState (propK s es k)).log.length :=
    bl_le_of_last C.length _ [] y s.term (fun j z hj hz => hs.2.2 j z hj (by simpa using hz)) hy hyt hT2
  have hlog : a.log = logAbs C C.length 1 (toPState (propK s es k)).log := hR.2.2.2.2.2.1
  refine ⟨hst, by rw [hlog, logAbs_length]; exact hbl, ?_, ?_⟩
  · obtain ⟨l0, hl0⟩ := List.getLast?_eq_some_iff.1 hy
    rw [hlog, hl0, logAbs_snoc]
    have hn : ¬ (1 + l0.length ≤ C.length) := by
      have : (toPState (propK s es k)).log.length = l0.length + 1 := by rw [hl0]; simp
      omega
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.map_some,
      entAbs, if_neg hn, hyt, hR.1]
    rfl
  · rw [hlog, logAbs_length, propK_len]
    have hb0 : uint.Z (toPState s).base.index' = 0 := by
      have := hs.1; simp only [toPState, propK, propAppended, logAppend] at this
      show uint.Z s.logst.prev.index' = 0; rw [this]; rfl
    simp only [plogLastIndexZ] at hbnd
    have := Nat.min_le_left k es.length
    omega

/-- **The facts kept by `ClientRequest`** (a `Replicate` line's step): a leader's log grows by a value
entry of its term (`repSrv`); its server facts (`srvFacts_rep`), the specification invariant
(`specInv_clientRequest`), `QuorumLogF` (`quorumLogF_grow`, with `CommitOk`), `AppSlices`
(`appSlices_extend`); the bags unchanged. -/
theorem simFx_replicate (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) (id : w64) (a : Etcdraft.Server)
    (hsrv : σ.server = confAbs C) (hidC : id ∈ C) (hσa : σ.s (idAbs id) = a)
    (hl : a.state = Etcdraft.leader) (hbl : C.length < a.log.length)
    (hlast : a.log.getLast?.map Etcdraft.Entry.term = some a.currentTerm) (hlen : a.log.length + 1 < 2 ^ 63) :
    simFx (GF := GF) γ C σ ⊢ simFx γ C (withNode σ (idAbs id) (repSrv a) _root_.id _root_.id) := by
  have hi : idAbs id ∈ σ.server := by rw [hsrv]; exact (mem_confAbs C id).2 hidC
  have hs' : ∀ j, (withNode σ (idAbs id) (repSrv a) _root_.id _root_.id).s j =
      if j = idAbs id then repSrv a else σ.s j := fun _ => rfl
  iintro #Hfx
  iunfold simFx at Hfx
  icases Hfx with ⟨#Hal, #Hmf, #Hq, %Hp⟩
  obtain ⟨hsi, hu, hsh, has⟩ := Hp
  icases allFacts_oneLeader γ C σ hsrv $$ Hal with %h1
  icases allFacts_commitOk γ C σ hsrv $$ Hal with %hco
  iunfold simFx
  isplitl
  · iunfold allFacts at Hal
    iunfold allFacts
    imodintro
    iintro %j %hj
    rw [hs']
    by_cases hji : idAbs j = idAbs id
    · rw [if_pos hji]
      have := idAbs_inj hji
      subst this
      iapply srvFacts_rep γ C j a hl hbl hlast hlen
      rw [← hσa]
      iapply Hal $$ %j %hj
    · rw [if_neg hji]
      iapply Hal $$ %j %hj
  isplitl
  · have hm : (withNode σ (idAbs id) (repSrv a) _root_.id _root_.id).messages = σ.messages := rfl
    have hp : (withNode σ (idAbs id) (repSrv a) _root_.id _root_.id).pendingMessages = σ.pendingMessages := rfl
    rw [hm, hp]
    imodintro; iexact Hmf
  have hL : ∀ k, (σ.s k).log <+: ((withNode σ (idAbs id) (repSrv a) _root_.id _root_.id).s k).log := by
    intro k; rw [hs']; split
    · rename_i h; subst h; rw [hσa]; exact List.prefix_append _ _
    · exact List.prefix_refl _
  have hC : ∀ k, ((withNode σ (idAbs id) (repSrv a) _root_.id _root_.id).s k).commitIndex = (σ.s k).commitIndex := by
    intro k; rw [hs']; split
    · rename_i h; subst h; rw [hσa]; rfl
    · rfl
  have hT : ∀ k, (σ.s k).currentTerm ≤ ((withNode σ (idAbs id) (repSrv a) _root_.id _root_.id).s k).currentTerm := by
    intro k; rw [hs']; split
    · rename_i h; subst h; rw [hσa]; exact Int.le_refl _
    · exact Int.le_refl _
  isplitl
  · iapply quorumLogF_grow γ C σ (withNode σ (idAbs id) (repSrv a) _root_.id _root_.id) rfl hL hC hT hco
    iexact Hq
  ipureintro
  have hcr : σ.clientRequest (idAbs id) 0 = some (σ.replicate (idAbs id) (.val 0) .value) := by
    unfold Etcdraft.State.clientRequest; simp [hσa, hl]
  have hrep : σ.replicate (idAbs id) (.val 0) .value = withNode σ (idAbs id) (repSrv a) _root_.id _root_.id := by
    rw [Etcdraft.State.replicate, upd_eq_withNode, hσa]; rfl
  rw [hrep] at hcr
  refine ⟨TraceSpecInv.specInv_clientRequest hsi hi h1 hcr, hu, hsh, ?_⟩
  exact appSlices_extend σ has (idAbs id) (repSrv a) (by rw [hσa]; rfl) (by rw [hσa]; rfl)
    (by rw [hσa]; exact List.prefix_append _ _)

/-- **A `Replicate` line's facts** at the pinned phases (the `k`-th of the batch): the share's server
`repSrv`'d (the pinned servers' `repC`), the list kept; `simFx_replicate` at the server's facts
(`simIdleS_repFacts`), then `simFx_congr` to the line's result. -/
theorem fxPres_replicate (γ : RaftNames) (id : w64) (E : TraceEv → Prop) (s : NState) (es : List EntryM)
    (o : List Msg) (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (hidC : id ∈ C0) (k : Nat)
    (hk : k < es.length) (hlead : s.role = .leader)
    (hlast : ∃ x, (toPState s).log.getLast? = some x ∧ x.Term' = s.term) (hT2 : 2 ≤ uint.Z s.term)
    (hbnd : plogLastIndexZ (toPState s).base (toPState s).log + es.length < 2 ^ 63) :
    ⊢ FxPres (GF := GF) γ id E (RepPin s es o C0 cs0 P0 k) (RepPin s es o C0 cs0 P0 (k + 1)) := by
  iunfold FxPres
  imodintro
  iintro %C %cs %P %e %a %a' %P' %σ %hpre Htbl #Hfx
  obtain ⟨⟨rfl, hcs, rfl, hI, -⟩, -, hca, ⟨-, hcs', hP', -⟩, -, hsrv, hσa, -, -, -⟩ := hpre
  have hP0 : P' = [] := by
    have := congrArg List.length hP'; rw [List.length_append] at this
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst hP0
  rw [← hca] at hI
  obtain ⟨hl, hbl, hlast', hlen⟩ := simIdleS_repFacts C s es k hk hlead hlast hT2 hbnd a hI
  ihave #H2 := simFx_replicate γ C σ id a hsrv hidC hσa hl hbl hlast' hlen $$ Hfx
  have hs : ∀ j, toC (withNode σ (idAbs id) (repSrv a) _root_.id _root_.id).server
      ((withNode σ (idAbs id) a' _root_.id (fun b => ([] : List Etcdraft.Msg).foldl Etcdraft.Bag.with b)).s j) =
      toC (withNode σ (idAbs id) (repSrv a) _root_.id _root_.id).server
        ((withNode σ (idAbs id) (repSrv a) _root_.id _root_.id).s j) := by
    intro j
    show toC σ.server (if j = idAbs id then a' else σ.s j) = toC σ.server (if j = idAbs id then repSrv a else σ.s j)
    split
    · rw [hsrv, hcs', toC_repSrv_eq, hca, hcs]; rfl
    · rfl
  ihave #H3 := simFx_congr γ C (withNode σ (idAbs id) (repSrv a) _root_.id _root_.id)
    (withNode σ (idAbs id) a' _root_.id (fun b => ([] : List Etcdraft.Msg).foldl Etcdraft.Bag.with b))
    rfl rfl rfl hs $$ H2
  iframe Htbl
  iexact H3

/-- **Sending keeps the facts**, the specification invariant given (`simFx_send` with `SpecInv` of the
result in place of `MsgOk`: an action whose step `specInv_*` proves, as `AppendEntriesToSelf`'s). -/
theorem simFx_sendS (γ : RaftNames) (C : List w64) (σ : Etcdraft.State) (x : Etcdraft.Msg)
    (hsi' : TraceSpecInv.SpecInv σ → TraceSpecInv.SpecInv (σ.send x)) (hx0 : canonMsg x = x)
    (hxk : ∀ y ∈ σ.messages.domain ++ σ.pendingMessages.domain, PinnedBy y x)
    (hxs : AppSliceOf σ x) :
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
  · iapply quorumLogF_congr γ C σ (σ.send x) rfl (fun _ => rfl) (fun _ => rfl) (fun _ => Int.le_refl _) $$ Hq
  ipureintro
  obtain ⟨hu', hsh'⟩ := msgsUniq_send_canon σ x hu hsh hx0 hxk
  exact ⟨hsi' hsi, hu', hsh', appSlices_send σ x has hxs⟩

/-- **The self-acknowledgement's facts** (`FxPres` of its `SendAppendEntriesResponse` line, at phases
keeping the share's server and adding its specification message `ma0`): the specification's
`AppendEntriesToSelf` (`appendEntriesToSelf_send`, `specInv_appendEntriesToSelf`) at a leader's idle
server of `s1`; the message plain (no entries, `msgFacts_plain`), canonical, pinning nothing. -/
theorem fxPres_selfAck (γ : RaftNames) (id : w64) (E : TraceEv → Prop) (s1 : NState)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) (C0 : List w64) (ma0 : Etcdraft.Msg)
    (hma : TraceSim.msgAbs C0 C0.length (selfAck id s1) = some ma0) (hrole : s1.role = .leader)
    (hC : ∀ C cs P, Φ C cs P → C = C0 ∧ id ∈ C ∧ SimIdleS C s1 cs)
    (hΦ' : ∀ C cs P cs' P', Φ C cs P → Φ' C cs' (P ++ P') → cs' = cs ∧ P' = [ma0]) :
    ⊢ FxPres (GF := GF) γ id E Φ Φ' := by
  iunfold FxPres
  imodintro
  iintro %C %cs %P %e %a %a' %P' %σ %hpre Htbl #Hfx
  obtain ⟨hΦ, -, hcs, hΦ1, -, hsrv, hσa, -, -, -⟩ := hpre
  obtain ⟨hcs', hP'⟩ := hΦ' C cs P _ P' hΦ hΦ1
  subst hP'
  obtain ⟨rfl, hidC, ⟨a0, ha0, hR0, hs, -⟩⟩ := hC C cs P hΦ
  have hR : SimServerR C C.length (toPState s1) (σ.s (idAbs id)) :=
    simServerR_toC (ha0.trans (hσa ▸ hcs).symm) hR0
  have hrl : (toPState s1).role = .leader := by rw [toPState_role, hrole]; rfl
  have hstep := appendEntriesToSelf_send σ C C.length (toPState s1) id hR hrl hs
  rw [selfAck_eq_pselfAck] at hma
  have hget : (TraceSim.msgAbs C C.length (pselfAck id (toPState s1))).get
      (by simp [TraceSim.msgAbs, pselfAck]) = ma0 := by simp only [hma, Option.get_some]
  rw [hget] at hstep
  have hty : ma0.type = .appendEntriesResponse := by
    simp only [TraceSim.msgAbs, pselfAck] at hma; cases hma; rfl
  have hen : ma0.entries = [] := by
    simp only [TraceSim.msgAbs, pselfAck] at hma; cases hma; rfl
  ihave #Hpf := msgFacts_plain (GF := GF) γ C ma0 (by rw [hty]; decide) hen
  ihave #H2 := simFx_sendS γ C σ ma0 (fun hsi => TraceSpecInv.specInv_appendEntriesToSelf hsi hstep)
    (msgAbs_canon C C.length _ ma0 hma) (fun _ _ h => absurd (h.symm.trans hty) (by decide))
    (appSliceOf_nil σ ma0 hen) $$ [$Hfx $Hpf]
  have hs' : ∀ j, toC (σ.send ma0).server
      ((withNode σ (idAbs id) a' _root_.id (fun b => [ma0].foldl Etcdraft.Bag.with b)).s j) =
      toC (σ.send ma0).server ((σ.send ma0).s j) := by
    intro j
    show toC σ.server (if j = idAbs id then a' else σ.s j) = toC σ.server (σ.s j)
    split
    · rename_i hj; subst hj; rw [hσa, hsrv, hcs', hcs]
    · rfl
  ihave #H3 := simFx_congr γ C (σ.send ma0)
    (withNode σ (idAbs id) a' _root_.id (fun b => [ma0].foldl Etcdraft.Bag.with b))
    rfl rfl rfl hs' $$ H2
  iframe Htbl
  iexact H3

end facts

end EtcdGrove
end Perennial
