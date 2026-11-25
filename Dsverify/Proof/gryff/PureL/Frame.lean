/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureL/Frame.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L: **the write-record frame** of the steps: every handler but the client requests, the
`Write1` handler and the write coordinator's reply handlers keeps the coordinator's write records
(`wops`), the replica's id and its used keys, and sends no `Write1` / `Write1Reply` (`FW`, `NoW`;
one lemma per handler, by `peel`, as `StoreSteps.lean`).
-/
module

public import Dsverify.Proof.gryff.PureL.StoreSteps

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto

/-- The messages of the write records' accounting. -/
def isWMsg : Msg → Bool
  | .write1 _ => true
  | .write1Reply _ => true
  | _ => false

def isWOut : Out → Bool
  | .send _ m => isWMsg m
  | .ext _ => false

/-- No `Write1` / `Write1Reply` among outputs. -/
def NoW (o : List Out) : Prop := ∀ x ∈ o, isWOut x = false

/-- The fields of the write accounting are kept. -/
def FW (s s' : RState) : Prop := s'.wops = s.wops ∧ s'.id = s.id ∧ s'.used = s.used

theorem FW.rfl' {s : RState} : FW s s := ⟨rfl, rfl, rfl⟩
theorem FW.trans' {a b c : RState} (h1 : FW a b) (h2 : FW b c) : FW a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

theorem noW_nil : NoW [] := by simp [NoW]
theorem noW_append {a b : List Out} (ha : NoW a) (hb : NoW b) : NoW (a ++ b) := by
  intro x hx; rcases List.mem_append.1 hx with h | h
  · exact ha x h
  · exact hb x h
theorem noW_single {x : Out} (h : isWOut x = false) : NoW [x] := by
  intro y hy; rw [List.mem_singleton.1 hy]; exact h
theorem noW_ext {x : Ext} : NoW [.ext x] := noW_single rfl

theorem sendTo_isW {q : w32} {m : Msg} {x : Out} (h : sendTo q m = some x) :
    isWOut x = isWMsg m := by
  unfold sendTo at h
  obtain ⟨d, _, rfl⟩ := Option.map_eq_some_iff.1 h; rfl

theorem sendPeer_isW {s : RState} {q : w32} {m : Msg} {x : Out} (h : sendPeer s q m = some x) :
    isWOut x = isWMsg m := by
  unfold sendPeer at h; split at h
  · cases h
  · exact sendTo_isW h

theorem mapM_some_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → ∀ y ∈ r, ∃ a ∈ l, f a = some y
  | [], r, h => by simp at h; subst h; simp
  | a :: l, r, h => by
    simp only [List.mapM_cons, bind, Option.bind] at h
    cases hfa : f a with
    | none => simp [hfa] at h
    | some b =>
      simp only [hfa] at h
      cases hl : l.mapM f with
      | none => simp [hl] at h
      | some bs =>
        simp only [hl, pure, Option.some.injEq] at h
        subst h
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact ⟨a, by simp, hfa⟩
        · obtain ⟨a', ha', h'⟩ := mapM_some_mem hl y hy
          exact ⟨a', by simp [ha'], h'⟩

theorem mapM_sendTo_isW {l : List w32} {m : Msg} {r : List Out}
    (h : l.mapM (fun q => sendTo q m) = some r) : ∀ y ∈ r, isWOut y = isWMsg m := by
  intro y hy
  obtain ⟨a, _, h'⟩ := mapM_some_mem h y hy
  exact sendTo_isW h'

theorem mapM_sendPeer_isW {s : RState} {l : List w32} {m : Msg} {r : List Out}
    (h : l.mapM (fun q => sendPeer s q m) = some r) : ∀ y ∈ r, isWOut y = isWMsg m := by
  intro y hy
  obtain ⟨a, _, h'⟩ := mapM_some_mem h y hy
  exact sendPeer_isW h'

theorem bcast_noW {s : RState} {m : Msg} {r : List Out} (h : bcast s m = some r)
    (hm : isWMsg m = false) : NoW r := by
  intro y hy; rw [mapM_sendPeer_isW h y hy]; exact hm

theorem bcastPreAccept_noW {s : RState} {a b c : w32} {cs : List Cmd} {sq : w32} {d : Deps}
    {v : ValTag} {r : List Out} (h : bcastPreAccept s a b c cs sq d v = some r) : NoW r :=
  bcast_noW h rfl
theorem bcastAccept_noW {s : RState} {a b c : w32} {cs : List Cmd} {sq : w32} {d : Deps}
    {v : ValTag} {r : List Out} (h : bcastAccept s a b c cs sq d v = some r) : NoW r :=
  bcast_noW h rfl
theorem bcastCommit_noW {s : RState} {a b : w32} {cs : List Cmd} {sq : w32} {d : Deps}
    {v : ValTag} {r : List Out} (h : bcastCommit s a b cs sq d v = some r) : NoW r :=
  bcast_noW h rfl
theorem bcastPrepare_noW {s : RState} {a b c : w32} {r : List Out}
    (h : bcastPrepare s a b c = some r) : NoW r :=
  bcast_noW h rfl

theorem updateConflicts_fw (s : RState) (cmds : List Cmd) (q i sq : w32) :
    FW s (updateConflicts s cmds q i sq) := by
  unfold updateConflicts
  apply forIn_id_inv (P := fun x : RState => FW s x) _ _ _ FW.rfl'
  intro a b hb
  simpa [FW] using hb

theorem updateCommitted_fw {s s' : RState} {q : w32} (h : updateCommitted s q = some s') :
    FW s s' := by
  unfold updateCommitted at h; opeel h
  all_goals (cases h; exact FW.rfl')

theorem overwrite_fw (s : RState) (v : w64) (t : model.Tag) : FW s (s.overwrite v t) := by
  unfold RState.overwrite; split <;> exact FW.rfl'

theorem updateConflicts_wops (s : RState) (cmds : List Cmd) (q i sq : w32) :
    (updateConflicts s cmds q i sq).wops = s.wops := (updateConflicts_fw s cmds q i sq).1
theorem updateConflicts_id (s : RState) (cmds : List Cmd) (q i sq : w32) :
    (updateConflicts s cmds q i sq).id = s.id := (updateConflicts_fw s cmds q i sq).2.1
theorem updateConflicts_used (s : RState) (cmds : List Cmd) (q i sq : w32) :
    (updateConflicts s cmds q i sq).used = s.used := (updateConflicts_fw s cmds q i sq).2.2
theorem overwrite_wops (s : RState) (v : w64) (t : model.Tag) : (s.overwrite v t).wops = s.wops :=
  (overwrite_fw s v t).1
theorem overwrite_id (s : RState) (v : w64) (t : model.Tag) : (s.overwrite v t).id = s.id :=
  (overwrite_fw s v t).2.1
theorem overwrite_used (s : RState) (v : w64) (t : model.Tag) : (s.overwrite v t).used = s.used :=
  (overwrite_fw s v t).2.2

macro "fw_fin_st" : tactic => `(tactic| (
  unfold FW
  try (have hu := updateCommitted_fw ‹updateCommitted _ _ = some _›; unfold FW at hu
       simp only [hu.1, hu.2.1, hu.2.2])
  try simp only [RState.setInst, RState.setCrt, updateConflicts_wops, updateConflicts_id,
    updateConflicts_used, overwrite_wops, overwrite_id, overwrite_used]
  try (have hu := updateCommitted_fw ‹updateCommitted _ _ = some _›; unfold FW at hu
       simp only [hu.1, hu.2.1, hu.2.2])
  try simp only [RState.setInst, RState.setCrt, updateConflicts_wops, updateConflicts_id,
    updateConflicts_used, overwrite_wops, overwrite_id, overwrite_used]
  try exact ⟨rfl, rfl, rfl⟩
  try exact ⟨trivial, trivial, trivial⟩))

macro "fw_fin" : tactic => `(tactic| (
  refine ⟨?_, ?_⟩
  · fw_fin_st
  · first
    | exact noW_nil
    | exact noW_ext
    | with_reducible exact bcastPreAccept_noW ‹_›
    | with_reducible exact bcastAccept_noW ‹_›
    | with_reducible exact bcastCommit_noW ‹_›
    | with_reducible exact bcastPrepare_noW ‹_›
    | with_reducible exact noW_single ((sendPeer_isW ‹sendPeer _ _ _ = some _›).trans rfl)
    | with_reducible exact noW_single ((sendTo_isW ‹sendTo _ _ = some _›).trans rfl)
    | (intro y hy; with_reducible exact (mapM_sendTo_isW ‹_› y hy).trans rfl)
    | (intro y hy; with_reducible exact (mapM_sendPeer_isW ‹_› y hy).trans rfl)))

theorem startPhase1_fw {s s' : RState} {q i b : w32} {ps : List Proposal} {cs : List Cmd}
    {o : List Out} (h : startPhase1 s q i b ps cs = .ok (s', o)) : FW s s' ∧ NoW o := by
  unfold startPhase1 at h; peel h
  all_goals (cases h; fw_fin)


theorem leaderCommit_fw {s s' : RState} {q i : w32} {c : Copy} {lb : LB} {o : List Out}
    (h : leaderCommit s q i c lb = .ok (s', o)) : FW s s' ∧ NoW o := by
  unfold leaderCommit at h; peel h
  all_goals (cases h; fw_fin)

macro "fw_close" h:ident : tactic => `(tactic| (
  peel $h:ident
  all_goals (first
    | (cases $h:ident; fw_fin; done)
    | (have hh := leaderCommit_fw $h:ident
       exact ⟨FW.trans' (by fw_fin_st) hh.1, hh.2⟩)
    | (have hh := startPhase1_fw $h:ident
       exact ⟨FW.trans' (by fw_fin_st) hh.1, hh.2⟩))))

theorem handleExecuted_fw {s s' : RState} {m : ExecutedM} {o : List Out}
    (h : handleExecuted s m = .ok (s', o)) : FW s s' ∧ NoW o := by
  unfold handleExecuted at h; fw_close h

theorem stepRead1Reply_fw {s s' : RState} {m : Read1ReplyM} {o : List Out}
    (h : stepRead1Reply s m = .ok (s', o)) : FW s s' ∧ NoW o := by
  unfold stepRead1Reply at h; fw_close h

theorem stepRead2Reply_fw {s s' : RState} {m : Read2ReplyM} {o : List Out}
    (h : stepRead2Reply s m = .ok (s', o)) : FW s s' ∧ NoW o := by
  unfold stepRead2Reply at h; fw_close h

theorem stepPreAccept_fw {s s' : RState} {m : PreAcceptM} {o : List Out}
    (h : stepPreAccept s m = .ok (s', o)) : FW s s' ∧ NoW o := by
  unfold stepPreAccept at h; fw_close h

theorem stepPreAcceptReply_fw {s s' : RState} {m : PreAcceptReplyM} {o : List Out}
    (h : stepPreAcceptReply s m = .ok (s', o)) : FW s s' ∧ NoW o := by
  unfold stepPreAcceptReply at h; fw_close h

theorem stepPreAcceptOK_fw {s s' : RState} {m : PreAcceptOKM} {o : List Out}
    (h : stepPreAcceptOK s m = .ok (s', o)) : FW s s' ∧ NoW o := by
  unfold stepPreAcceptOK at h; fw_close h

theorem stepAccept_fw {s s' : RState} {m : EAcceptM} {o : List Out}
    (h : stepAccept s m = .ok (s', o)) : FW s s' ∧ NoW o := by
  unfold stepAccept at h; fw_close h

theorem stepAcceptReply_fw {s s' : RState} {m : AcceptReplyM} {o : List Out}
    (h : stepAcceptReply s m = .ok (s', o)) : FW s s' ∧ NoW o := by
  unfold stepAcceptReply at h; fw_close h

theorem stepCommit_fw {s s' : RState} {m : ECommitM} {o : List Out}
    (h : stepCommit s m = .ok (s', o)) : FW s s' ∧ NoW o := by
  unfold stepCommit at h; fw_close h

theorem stepPrepare_fw {s s' : RState} {m : PrepareM} {o : List Out}
    (h : stepPrepare s m = .ok (s', o)) : FW s s' ∧ NoW o := by
  unfold stepPrepare at h; fw_close h

theorem stepPrepareReply_fw {s s' : RState} {m : PrepareReplyM} {o : List Out}
    (h : stepPrepareReply s m = .ok (s', o)) : FW s s' ∧ NoW o := by
  unfold stepPrepareReply at h; fw_close h

theorem stepRecover_fw {s s' : RState} {q i : w32} {o : List Out}
    (h : stepRecover s q i = .ok (s', o)) : FW s s' ∧ NoW o := by
  unfold stepRecover at h; fw_close h

theorem stepExec_fw {s s' : RState} {q i : w32} {o : List Out}
    (h : stepExec s q i = .ok (s', o)) : FW s s' ∧ NoW o := by
  unfold stepExec at h; fw_close h

theorem stepRead1_fw {s s' : RState} {m : Read1ProxiedM} {o : List Out}
    (h : stepRead1 s m = .ok (s', o)) : FW s s' ∧ NoW o := by
  unfold stepRead1 at h; fw_close h

theorem stepRead2_fw {s s' : RState} {m : Read2ProxiedM} {o : List Out}
    (h : stepRead2 s m = .ok (s', o)) : FW s s' ∧ NoW o := by
  unfold stepRead2 at h; fw_close h

theorem stepWrite2_fw {s s' : RState} {m : Write2ProxiedM} {o : List Out}
    (h : stepWrite2 s m = .ok (s', o)) : FW s s' ∧ NoW o := by
  unfold stepWrite2 at h; fw_close h

theorem stepExecuteOverwrite_fw {s s' : RState} {m : ExecuteOverwriteM} {o : List Out}
    (h : stepExecuteOverwrite s m = .ok (s', o)) : FW s s' ∧ NoW o := by
  unfold stepExecuteOverwrite at h
  peel h
  all_goals (first
    | (cases h; fw_fin; done)
    | (have hh := handleExecuted_fw h
       exact ⟨FW.trans' (by fw_fin_st) hh.1, hh.2⟩))


/-! ## The write path's handlers -/

namespace AMap
theorem get?_put {n : Nat} {V : Type} (m : model.AMap n V) (k k' : BitVec n) (v : V) :
    (m.put k v).get? k' = if k' = k then some v else m.get? k' := by
  induction m with
  | nil => simp [model.AMap.put, model.AMap.get?, List.lookup]; split <;> simp_all
  | cons e t ih =>
    obtain ⟨k0, v0⟩ := e
    unfold model.AMap.put
    by_cases h1 : k = k0
    · subst h1; simp only [model.AMap.get?, List.lookup, if_pos]
      by_cases h : k' = k
      · simp [h]
      · have : (k' == k) = false := by simp [h]
        simp [this, h]
    · simp only [h1, if_false]
      split
      · simp only [model.AMap.get?, List.lookup]
        by_cases h : k' = k
        · subst h; simp
        · have : (k' == k) = false := by simp [h]
          simp [this, h]
      · simp only [model.AMap.get?, List.lookup] at ih ⊢
        rw [ih]
        by_cases h : k' = k0
        · subst h; simp [h1]; intro h'; exact absurd h'.symm h1
        · have : (k' == k0) = false := by simp [h]
          simp [this]

theorem get?_del {n : Nat} {V : Type} (m : model.AMap n V) (k k' : BitVec n) :
    (m.del k).get? k' = if k' = k then none else m.get? k' := by
  induction m with
  | nil => simp [model.AMap.del, model.AMap.get?, List.lookup]
  | cons e t ih =>
    obtain ⟨k0, v0⟩ := e
    simp only [model.AMap.del, model.AMap.get?] at ih ⊢
    rw [List.filter_cons]
    by_cases h : k0 = k
    · subst h; simp only [bne_self_eq_false, Bool.false_eq_true, if_false, ih]
      by_cases h' : k' = k0
      · simp [h']
      · have : (k' == k0) = false := by simp [h']
        simp [List.lookup, this, h']
    · have hb : (k0 != k) = true := by simp [h]
      simp only [hb, if_true, List.lookup, ih]
      by_cases h' : k' = k0
      · subst h'; simp [h]
      · have : (k' == k0) = false := by simp [h']
        simp [this]
end AMap

theorem sendTo_out {q : w32} {m : Msg} {x : Out} (h : sendTo q m = some x) :
    ∃ d, dstOf q = some d ∧ x = .send d m := by
  unfold sendTo at h
  obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.1 h; exact ⟨d, hd, rfl⟩

theorem stepClientWrite_spec {s s' : RState} {rid cid : w32} {k v : w64} {d : Dep} {o : List Out}
    (h : stepClientWrite s rid cid k v d = .ok (s', o)) :
    (cid, rid) ∉ s.used ∧ 0 ≤ sint.Z cid ∧ s'.used = (cid, rid) :: s.used ∧ s'.id = s.id ∧
    (∃ w : WriteOp, w.numWrite1Replies = 0 ∧ w.writeTag = none ∧
      s'.wops = s.wops.put (shiftInts rid cid) w) ∧
    ∃ m : Write1ProxiedM, m.requestId = rid ∧ m.clientId = cid ∧ m.replicaId = s.id ∧
      o = [.send 0 (.write1 m), .send 1 (.write1 m), .send 2 (.write1 m)] := by
  unfold stepClientWrite at h
  peel h
  cases h
  rename_i hg _ hu _ hm
  refine ⟨hu, ?_, rfl, rfl, ⟨_, rfl, rfl, rfl⟩,
    { requestId := rid, clientId := cid, forceWrite := 1, k := 0, d := d, replicaId := s.id }, rfl, rfl, rfl, ?_⟩
  · simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, sge, sle,
      decide_eq_true_eq] at hg
    exact hg.2
  · simp [List.mapM_cons, sendTo, dstOf, sint.Z] at hm
    rw [← hm]; rfl

theorem stepWrite1_spec {s s' : RState} {m : Write1ProxiedM} {o : List Out}
    (h : stepWrite1 s m = .ok (s', o)) : FW s s' ∧ (o = [] ∨ ∃ x,
      sendTo m.replicaId (.write1Reply ⟨m.requestId, m.clientId, ⟨-1, s'.tag⟩⟩) = some x ∧
      o = [x]) := by
  unfold stepWrite1 at h
  peel h
  all_goals (cases h)
  all_goals (first
    | exact ⟨by fw_fin_st, Or.inl rfl⟩
    | exact ⟨by fw_fin_st, Or.inr ⟨_, ‹_›, rfl⟩⟩)

theorem shortCircuit_fw {s s' : RState} {n : w32} {v : ValTag} {f : Bool} {o : List Out}
    (h : shortCircuit s n v f = some (s', o)) : FW s s' ∧ NoW o := by
  rcases Perennial.gryff.model.shortCircuit_cases h with h | ⟨rfl, rfl⟩
  rotate_left
  · exact ⟨FW.rfl', noW_nil⟩
  unfold Perennial.gryff.model.shortCircuitReads at h
  opeel h
  all_goals
    cases h
    refine forIn_opt_inv _ _ _ (fun p : RState × List Out => FW s p.1 ∧ NoW p.2)
      ⟨⟨rfl, rfl, rfl⟩, noW_nil⟩ ?_ _ ‹_›
    intro a b st hb hf
    opeel hf
    all_goals (cases hf; first
      | exact hb
      | exact ⟨hb.1, noW_append hb.2 noW_ext⟩)

theorem shortCircuit_ite_fw {s s' : RState} {c : Prop} [Decidable c] {n : w32} {v : ValTag}
    {f : Bool} {o : List Out}
    (h : (if c then shortCircuit s n v f else some (s, [])) = some (s', o)) : FW s s' ∧ NoW o := by
  split at h
  · exact shortCircuit_fw h
  · cases h; exact ⟨FW.rfl', noW_nil⟩

/-- What the `Write1Reply` handler does to the write records. -/
def W1RSpec (s s' : RState) (m : Write1ReplyM) : Prop :=
  let K := shiftInts m.requestId m.clientId
  (∀ K', K' ≠ K → s'.wops.get? K' = s.wops.get? K') ∧
  (s.wops.get? K = none → s'.wops.get? K = none) ∧
  ∀ w', s'.wops.get? K = some w' → ∃ w, s.wops.get? K = some w ∧
    w'.numWrite1Replies = w.numWrite1Replies + 1 ∧
    w'.maxValTag.t = (if m.vt.t.gt w.maxValTag.t then m.vt.t else w.maxValTag.t) ∧
    (w'.writeTag = w.writeTag ∨ (sge w'.numWrite1Replies (NHALF + 1) = true ∧
      ∃ c, w'.writeTag = some ⟨w'.maxValTag.t.ts + 1, c, 0⟩))

theorem stepWrite1Reply_spec {s s' : RState} {m : Write1ReplyM} {o : List Out}
    (h : stepWrite1Reply s m = .ok (s', o)) :
    s'.id = s.id ∧ s'.used = s.used ∧ NoW o ∧ W1RSpec s s' m := by
  unfold stepWrite1Reply at h
  peel h
  all_goals (cases h)
  all_goals (try (have hsc := shortCircuit_fw ‹shortCircuit _ _ _ _ = some _›
                  obtain ⟨⟨hf1, hf2, hf3⟩, hn⟩ := hsc))
  all_goals (refine ⟨?_, ?_, ?_, fun K' hK' => ?_, fun hN => ?_, fun w' hw' => ?_⟩)
  all_goals (first
    | rfl
    | exact hf2
    | exact hf3
    | exact noW_nil
    | exact noW_append hn noW_ext
    | (intro y hy; exact (mapM_sendTo_isW ‹_› y hy).trans rfl)
    | (simp only [hf1, AMap.get?_put, AMap.get?_del, hK', if_false]; done)
    | (simp only [AMap.get?_put, AMap.get?_del, hK', if_false]; done)
    | exact hN
    | (simp_all [AMap.get?_put, AMap.get?_del]; done)
    | (simp only [AMap.get?_put, AMap.get?_del, if_true, Option.some.injEq, reduceCtorEq] at hw')
    | skip)
  all_goals (subst hw'; refine ⟨_, ‹_›, ?_⟩; simp_all)

/-- What the `Write2Reply` handler does to the write records. -/
def W2RSpec (s s' : RState) (m : Write2ReplyM) : Prop :=
  let K := shiftInts m.requestId m.clientId
  (∀ K', K' ≠ K → s'.wops.get? K' = s.wops.get? K') ∧
  (s.wops.get? K = none → s'.wops.get? K = none) ∧
  ∀ w', s'.wops.get? K = some w' → ∃ w, s.wops.get? K = some w ∧
    w'.numWrite1Replies = w.numWrite1Replies ∧ w'.maxValTag = w.maxValTag ∧
    w'.writeTag = w.writeTag

theorem stepWrite2Reply_spec {s s' : RState} {m : Write2ReplyM} {o : List Out}
    (h : stepWrite2Reply s m = .ok (s', o)) :
    s'.id = s.id ∧ s'.used = s.used ∧ NoW o ∧ W2RSpec s s' m := by
  unfold stepWrite2Reply at h
  peel h
  all_goals (cases h)
  all_goals (try (have hsc := shortCircuit_ite_fw ‹(if _ then shortCircuit _ _ _ _ else some _) = some _›
                  obtain ⟨⟨hf1, hf2, hf3⟩, hn⟩ := hsc))
  all_goals (refine ⟨?_, ?_, ?_, fun K' hK' => ?_, fun hN => ?_, fun w' hw' => ?_⟩)
  all_goals (first
    | rfl
    | exact hf2
    | exact hf3
    | exact noW_nil
    | exact noW_append hn noW_ext
    | (intro y hy; exact (mapM_sendTo_isW ‹_› y hy).trans rfl)
    | (simp only [hf1, AMap.get?_put, AMap.get?_del, hK', if_false]; done)
    | (simp only [AMap.get?_put, AMap.get?_del, hK', if_false]; done)
    | exact hN
    | (simp_all [AMap.get?_put, AMap.get?_del]; done)
    | (simp only [AMap.get?_put, AMap.get?_del, if_true, Option.some.injEq, reduceCtorEq] at hw')
    | skip)
  all_goals (subst hw'; refine ⟨_, ‹_›, ?_⟩; simp_all)

/-- A client read or RMW request's effect on the write accounting. -/
def CR (s s' : RState) (cid rid : w32) (o : List Out) : Prop :=
  (cid, rid) ∉ s.used ∧ 0 ≤ sint.Z cid ∧ s'.used = (cid, rid) :: s.used ∧ s'.id = s.id ∧
    s'.wops = s.wops ∧ NoW o

theorem stepClientRead_spec {s s' : RState} {rid cid : w32} {k : w64} {d : Dep} {o : List Out}
    (h : stepClientRead s rid cid k d = .ok (s', o)) : CR s s' cid rid o := by
  unfold stepClientRead at h
  peel h
  cases h
  have hx := ‹forIn _ _ _ = Except.ok s'›
  have hm := ‹List.mapM _ _ = some o›
  have hu := ‹¬(cid, rid) ∈ s.used›
  have hg := ‹¬(!(_ && _ && _)) = true›
  have hP : s'.used = (cid, rid) :: s.used ∧ s'.id = s.id ∧ s'.wops = s.wops := by
    refine forIn_exc_inv _ _ _ (fun x : RState => x.used = (cid, rid) :: s.used ∧ x.id = s.id ∧
      x.wops = s.wops) ?_ ?_ _ hx
    · exact ⟨rfl, rfl, rfl⟩
    intro a b st hb hf
    peel hf
    all_goals (cases hf; exact hb)
  refine ⟨hu, ?_, hP.1, hP.2.1, hP.2.2, ?_⟩
  · simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, sge, sle,
      decide_eq_true_eq] at hg
    exact hg.2
  · intro y hy; exact (mapM_sendPeer_isW hm y hy).trans rfl

theorem stepClientRMW_spec {s s' : RState} {rid cid : w32} {k : w64} {d : Dep} {a b : w64}
    {o : List Out} (h : stepClientRMW s rid cid k d a b = .ok (s', o)) : CR s s' cid rid o := by
  unfold stepClientRMW at h
  peel h
  obtain ⟨-, -, h⟩ := handlePropose_ok h; unfold handleProposeBody at h
  have hh := startPhase1_fw h
  have hu := ‹¬(cid, rid) ∈ s.used›
  have hg := ‹¬(!(_ && _ && _)) = true›
  refine ⟨hu, ?_, ?_, ?_, ?_, hh.2⟩
  · simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, sge, sle,
      decide_eq_true_eq] at hg
    exact hg.2
  · rw [hh.1.2.2]; rfl
  · rw [hh.1.2.1]; rfl
  · rw [hh.1.1]; rfl

/-- The events with their own write-accounting lemma. -/
def Ev.wspecial : Ev → Bool
  | .read .. => true
  | .write .. => true
  | .rmw .. => true
  | .msg (.write1 _) => true
  | .msg (.write1Reply _) => true
  | .msg (.write2Reply _) => true
  | _ => false

/-- Every other step keeps the write accounting. -/
theorem step_fw_other {r : Fin 3} {s s' : RState} {e : Ev} {o : List Out}
    (h : stepR r s e = .ok (s', o)) (he : Ev.wspecial e = false) : FW s s' ∧ NoW o := by
  cases e with
  | read => cases he
  | write => cases he
  | rmw => cases he
  | forceWrite => cases h; exact ⟨FW.rfl', noW_nil⟩
  | recover => exact stepRecover_fw h
  | exec => exact stepExec_fw h
  | msg m =>
    cases m with
    | read1 => exact stepRead1_fw h
    | read2 => exact stepRead2_fw h
    | write1 => cases he
    | write2 => exact stepWrite2_fw h
    | read1Reply => exact stepRead1Reply_fw h
    | read2Reply => exact stepRead2Reply_fw h
    | write1Reply => cases he
    | write2Reply => cases he
    | prepare => exact stepPrepare_fw h
    | preAccept => exact stepPreAccept_fw h
    | accept => exact stepAccept_fw h
    | commit => exact stepCommit_fw h
    | prepareReply => exact stepPrepareReply_fw h
    | preAcceptReply => exact stepPreAcceptReply_fw h
    | preAcceptOK => exact stepPreAcceptOK_fw h
    | acceptReply => exact stepAcceptReply_fw h
    | executed => exact handleExecuted_fw h
    | executeOverwrite => exact stepExecuteOverwrite_fw h

end Perennial.gryff.pure
