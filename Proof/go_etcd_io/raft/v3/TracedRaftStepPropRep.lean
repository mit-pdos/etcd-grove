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
    (hxt : x.Term' = T) (hT : 2 ≤ uint.Z T) : bl ≤ l.length := by
  rcases Nat.lt_or_ge l.length bl with h | h
  · exfalso
    obtain ⟨l0, hl0⟩ := List.getLast?_eq_some_iff.1 hlast
    have hk : (l ++ l')[l0.length]? = some x := by
      rw [hl0, List.append_assoc]; simp
    have hlen : l.length = l0.length + 1 := by rw [hl0]; simp
    have := hshape l0.length x (by omega) hk
    rw [hxt] at this
    subst this
    have : uint.Z (W64 1) = 1 := rfl
    omega
  · exact h

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
  have hbl0 : C.length ≤ (toPState s).log.length :=
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

end EtcdGrove
end Perennial
