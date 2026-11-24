/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLc/Vals.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-c: **L3, the values invariant** (per step). Every `(value, tag)` pair carried by a state or
a message satisfies a predicate `Q` (at run level: `Prod l` with `0 ≤ rmwc`): stores,
`PrevValTag`, copies' and recovery candidates' bases, read records' `maxValTag`/`readValTag`,
write records' `(writeValue, WriteTag)`; `Read1`/`Read2`/`Read1Reply`/`Write2` pairs, the EPaxos
messages' bases, `ExecuteOverwrite`. Write records keep `numWrite1Applies = 0` and a `maxValTag`
of value `-1` (the `Write1Reply`s carry `-1`), so the `Write1Reply` fast path never fires.

Sources (hypotheses of the step lemmas): an execution's result (`stepExec`), a new `WriteTag`
with the record's value (`stepWrite1Reply`), and `(0, tag0)`.
-/
module

public import Dsverify.Proof.gryff.PureLc.Cmds

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto

section
variable (Q : w64 → model.Tag → Prop)

def QV (vt : ValTag) : Prop := Q vt.v vt.t

def VCopy (cp : Copy) : Prop :=
  QV Q cp.base ∧ ∀ lb ir, cp.lb = some lb → lb.recoveryInst = some ir → QV Q ir.base

def VRd (rd : ReadOp) : Prop :=
  (∀ vt, rd.maxValTag = some vt → QV Q vt) ∧ (∀ vt, rd.readValTag = some vt → QV Q vt)

def VWr (w : WriteOp) : Prop :=
  w.numWrite1Applies = 0 ∧ w.maxValTag.v = -1 ∧ (w.sentWrite2Round = false → w.writeTag = none) ∧
    ∀ wt, w.writeTag = some wt → Q w.writeValue wt

/-- The values invariant of a state. -/
structure VS (s : RState) : Prop where
  store : Q s.val s.tag
  prev : ∀ vt, s.prevValTag = some vt → QV Q vt
  inst : ∀ q i cp, s.inst q i = some cp → VCopy Q cp
  rops : ∀ K rd, s.rops.get? K = some rd → VRd Q rd
  wops : ∀ K w, s.wops.get? K = some w → VWr Q w

/-- The values invariant of a message. -/
def VM : Msg → Prop
  | .read1 m => QV Q m.vt ∧ QV Q m.d.vt
  | .read2 m => QV Q m.vt
  | .read1Reply m => QV Q m.vt
  | .write1 m => sge m.d.key 0 = true → QV Q m.d.vt
  | .write1Reply m => m.vt.v = -1
  | .write2 m => QV Q m.vt
  | .preAccept m => QV Q m.base
  | .preAcceptReply m => QV Q m.base
  | .accept m => QV Q m.base
  | .commit m => QV Q m.base
  | .prepareReply m => QV Q m.base
  | .executeOverwrite m => Q m.v m.t
  | _ => True

def VO (o : List Out) : Prop := ∀ x ∈ o, match x with
  | .send _ m => VM Q m
  | .ext _ => True

end

section
variable {Q : w64 → model.Tag → Prop}

theorem VO.nil : VO Q [] := by simp [VO]
theorem VO.append {a b : List Out} (ha : VO Q a) (hb : VO Q b) : VO Q (a ++ b) := by
  intro x hx; rcases List.mem_append.1 hx with h | h
  · exact ha x h
  · exact hb x h
theorem VO.ext {x : Ext} : VO Q [.ext x] := by simp [VO]

theorem VO.ofSendTo {q : w32} {m : Msg} {x : Out} (h : sendTo q m = some x) (hm : VM Q m) :
    VO Q [x] := by
  obtain ⟨d, rfl⟩ := sendTo_some h
  intro y hy; rw [List.mem_singleton.1 hy]; exact hm

theorem VO.ofSendPeer {s : RState} {q : w32} {m : Msg} {x : Out} (h : sendPeer s q m = some x)
    (hm : VM Q m) : VO Q [x] := by
  unfold sendPeer at h; split at h
  · cases h
  · exact VO.ofSendTo h hm

theorem VO.ofBcast {s : RState} {m : Msg} {r : List Out} (h : bcast s m = some r) (hm : VM Q m) :
    VO Q r := by
  intro y hy
  obtain ⟨q, -, hq⟩ := mapM_some_mem h y hy
  unfold sendPeer at hq; split at hq
  · cases hq
  · obtain ⟨d, rfl⟩ := sendTo_some hq; exact hm

theorem VO.ofMapSendTo {l : List w32} {m : Msg} {r : List Out}
    (h : l.mapM (fun q => sendTo q m) = some r) (hm : VM Q m) : VO Q r := by
  intro y hy
  obtain ⟨q, -, hq⟩ := mapM_some_mem h y hy
  obtain ⟨d, rfl⟩ := sendTo_some hq; exact hm

theorem VO.ofMapSendPeer {s : RState} {l : List w32} {m : Msg} {r : List Out}
    (h : l.mapM (fun q => sendPeer s q m) = some r) (hm : VM Q m) : VO Q r := by
  intro y hy
  obtain ⟨q, -, hq⟩ := mapM_some_mem h y hy
  unfold sendPeer at hq; split at hq
  · cases hq
  · obtain ⟨d, rfl⟩ := sendTo_some hq; exact hm

theorem qs_ow {s : RState} (hs : Q s.val s.tag) {v : w64} {t : model.Tag} (h : Q v t) :
    Q (s.overwrite v t).val (s.overwrite v t).tag := by
  unfold RState.overwrite; split
  · exact h
  · exact hs

/-- What a short circuit keeps: everything but the deleted read records and `OngoingReqs`. -/
def SCF (s s' : RState) : Prop :=
  s'.val = s.val ∧ s'.tag = s.tag ∧ s'.prevValTag = s.prevValTag ∧ s'.inst = s.inst ∧
    s'.wops = s.wops ∧ ∀ K rd, s'.rops.get? K = some rd → s.rops.get? K = some rd

theorem SCF.r {s s' : RState} (h : SCF s s') : ∀ K rd, s'.rops.get? K = some rd →
    s.rops.get? K = some rd := h.2.2.2.2.2

theorem shortCircuit_v {s s' : RState} {n : w32} {v : ValTag} {f : Bool} {o : List Out}
    (h : shortCircuit s n v f = some (s', o)) : SCF s s' ∧ VO Q o := by
  unfold shortCircuit at h
  opeel h
  all_goals
    cases h
    refine forIn_opt_inv _ _ _ (fun p : RState × List Out => SCF s p.1 ∧ VO Q p.2)
      ⟨⟨rfl, rfl, rfl, rfl, rfl, fun K rd h => h⟩, VO.nil⟩ ?_ _ ‹_›
    intro a b st hb hf
    opeel hf
    all_goals (cases hf; first
      | exact hb
      | (obtain ⟨⟨e1, e2, e3, e4, e5, e6⟩, ho⟩ := hb
         refine ⟨⟨e1, e2, e3, e4, e5, fun K rd h => e6 K rd ?_⟩, VO.append ho VO.ext⟩
         try simp only [ForInStep.value, AMap.get?_del] at h
         try split at h
         all_goals first | cases h | exact h))

theorem shortCircuit_ite_v {s s' : RState} {c : Prop} [Decidable c] {n : w32} {v : ValTag}
    {f : Bool} {o : List Out}
    (h : (if c then shortCircuit s n v f else some (s, [])) = some (s', o)) :
    SCF s s' ∧ VO Q o := by
  split at h
  · exact shortCircuit_v h
  · cases h; exact ⟨⟨rfl, rfl, rfl, rfl, rfl, fun K rd h => h⟩, VO.nil⟩

theorem updateCommitted_v {s s' : RState} {q : w32} (h : updateCommitted s q = some s') :
    s'.val = s.val ∧ s'.tag = s.tag ∧ s'.prevValTag = s.prevValTag ∧ s'.inst = s.inst ∧
      s'.rops = s.rops ∧ s'.wops = s.wops := by
  unfold updateCommitted at h; opeel h
  all_goals (cases h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

theorem updateConflicts_v (s : RState) (cmds : List Cmd) (q i sq : w32) :
    (updateConflicts s cmds q i sq).val = s.val ∧ (updateConflicts s cmds q i sq).tag = s.tag ∧
    (updateConflicts s cmds q i sq).prevValTag = s.prevValTag ∧
    (updateConflicts s cmds q i sq).inst = s.inst ∧
    (updateConflicts s cmds q i sq).rops = s.rops ∧ (updateConflicts s cmds q i sq).wops = s.wops := by
  unfold updateConflicts
  apply forIn_id_inv (P := fun x : RState => x.val = s.val ∧ x.tag = s.tag ∧
    x.prevValTag = s.prevValTag ∧ x.inst = s.inst ∧ x.rops = s.rops ∧ x.wops = s.wops) _ _ _
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  intro a b hb
  simpa using hb

theorem uc_val (s : RState) (cmds : List Cmd) (q i sq : w32) :
    (updateConflicts s cmds q i sq).val = s.val := (updateConflicts_v s cmds q i sq).1
theorem uc_tag (s : RState) (cmds : List Cmd) (q i sq : w32) :
    (updateConflicts s cmds q i sq).tag = s.tag := (updateConflicts_v s cmds q i sq).2.1
theorem uc_prev (s : RState) (cmds : List Cmd) (q i sq : w32) :
    (updateConflicts s cmds q i sq).prevValTag = s.prevValTag := (updateConflicts_v s cmds q i sq).2.2.1
theorem uc_inst (s : RState) (cmds : List Cmd) (q i sq : w32) :
    (updateConflicts s cmds q i sq).inst = s.inst := (updateConflicts_v s cmds q i sq).2.2.2.1
theorem uc_rops (s : RState) (cmds : List Cmd) (q i sq : w32) :
    (updateConflicts s cmds q i sq).rops = s.rops := (updateConflicts_v s cmds q i sq).2.2.2.2.1
theorem uc_wops (s : RState) (cmds : List Cmd) (q i sq : w32) :
    (updateConflicts s cmds q i sq).wops = s.wops := (updateConflicts_v s cmds q i sq).2.2.2.2.2

theorem ow_rops (s : RState) (v : w64) (t : model.Tag) : (s.overwrite v t).rops = s.rops := by
  unfold RState.overwrite; split <;> rfl

end

/-! ## Closing tactics (hygiene off: they use `hs : VS Q s`, `hm`, `hq0`, `hsrc`) -/

set_option hygiene false in
/-- Normalize the components of a handler's new state. -/
macro "vk_norm" : tactic => `(tactic| (
  try (refine (fun hu => ?_) (updateCommitted_v ‹updateCommitted _ _ = some _›)
       obtain ⟨u1, u2, u3, u4, u5, u6⟩ := hu
       simp only [u1, u2, u3, u4, u5, u6] at *)
  try (refine (fun hu => ?_) (shortCircuit_v (Q := Q) ‹shortCircuit _ _ _ _ = some _›)
       obtain ⟨⟨u1, u2, u3, u4, u5, u6⟩, -⟩ := hu
       simp only [u1, u2, u3, u4, u5] at *)
  try (refine (fun hu => ?_) (shortCircuit_ite_v (Q := Q)
         ‹(if _ then shortCircuit _ _ _ _ else some _) = some _›)
       obtain ⟨⟨u1, u2, u3, u4, u5, u6⟩, -⟩ := hu
       simp only [u1, u2, u3, u4, u5] at *)
  try simp only [RState.setInst, RState.setCrt, uc_val, uc_tag, uc_prev, uc_inst, uc_rops,
    uc_wops, overwrite_prev, overwrite_inst, overwrite_wops, ow_rops, RState.storeVT, QV, VCopy,
    VRd, VWr] at *))

/-- A pair `Q v t` from the hypotheses. -/
syntax "vk_pair" : tactic

set_option hygiene false in
macro_rules | `(tactic| vk_pair) => `(tactic| (first
  | assumption
  | exact hq0
  | exact hs.store
  | exact hm.1
  | exact hm.2
  | exact hs.prev _ ‹_›
  | exact hlb0 _ ‹_›
  | exact (hs.rops _ _ ‹s.rops.get? _ = some _›).1 _ ‹_›
  | exact (hs.rops _ _ ‹s.rops.get? _ = some _›).2 _ ‹_›
  | exact (hs.inst _ _ _ ‹s.inst _ _ = some _›).1
  | exact (hs.inst _ _ _ ‹s.inst _ _ = some _›).2 _ _ ‹_› ‹_›
  | (apply qs_ow <;> vk_pair)
  | (simp only [vt0, model.tag0] at *; exact hq0)
  | (subst_vars; first
      | assumption
      | exact hs.store
      | exact (hs.inst _ _ _ ‹s.inst _ _ = some _›).1
      | exact (hs.inst _ _ _ ‹s.inst _ _ = some _›).2 _ _ ‹_› ‹_›)))

set_option hygiene false in
macro "vk_copy" : tactic => `(tactic| (first
  | exact hs.inst _ _ _ ‹s.inst _ _ = some _›
  | (refine ⟨?_, fun lb ir hlb hir => ?_⟩
     · try simp only [riOf] at *
       vk_pair
     · try simp only at hlb
       first
         | (cases hlb; done)
         | exact (hs.inst _ _ _ ‹s.inst _ _ = some _›).2 lb ir hlb hir
         | (cases hlb; try simp only at hir
            first
              | (cases hir; done)
              | (cases hir; try simp only [riOf] at *; vk_pair)
              | vk_pair))))

set_option hygiene false in
macro "vk_inst" : tactic => `(tactic| (
  intro q i cp hcp
  try simp only [RState.setInst, RState.setCrt] at hcp
  repeat' (split at hcp)
  all_goals first
    | exact hs.inst _ _ _ hcp
    | (cases hcp
       rename_i hqi
       obtain ⟨rfl, rfl⟩ := hqi
       vk_copy)))

set_option hygiene false in
macro "vk_out" : tactic => `(tactic| (first
  | exact VO.nil
  | exact VO.ext
  | (apply VO.ofSendPeer ‹sendPeer _ _ _ = some _›; first | trivial | (simp only [VM, QV]; vk_pair))
  | (apply VO.ofSendTo ‹sendTo _ _ = some _›; first | trivial | (simp only [VM, QV]; vk_pair))
  | (apply VO.ofBcast ‹bcast _ _ = some _›; first | trivial | (simp only [VM, QV]; vk_pair))
  | (apply VO.ofBcast ‹bcastPreAccept _ _ _ _ _ _ _ _ = some _›; simp only [VM, QV]; vk_pair)
  | (apply VO.ofBcast ‹bcastAccept _ _ _ _ _ _ _ _ = some _›; simp only [VM, QV]; vk_pair)
  | (apply VO.ofBcast ‹bcastCommit _ _ _ _ _ _ _ = some _›; simp only [VM, QV]; vk_pair)
  | (apply VO.ofBcast ‹bcastPrepare _ _ _ _ = some _›; trivial)
  | (apply VO.ofMapSendTo ‹List.mapM _ _ = some _›; first | trivial | (simp only [VM, QV]; vk_pair))
  | (apply VO.ofMapSendPeer ‹List.mapM _ _ = some _›; first | trivial | (simp only [VM, QV]; vk_pair))))

set_option hygiene false in
/-- A field of a read record: from the message, or the old record's. -/
macro "vk_rdf" : tactic => `(tactic| (
  intro vt hvt
  try simp only at hvt
  first
    | (cases hvt; vk_pair)
    | exact (hs.rops _ _ ‹s.rops.get? _ = some _›).1 vt hvt
    | exact (hs.rops _ _ ‹s.rops.get? _ = some _›).2 vt hvt
    | (cases hvt; done)
    | (subst_vars; first
        | exact (hs.rops _ _ ‹s.rops.get? _ = some _›).1 vt hvt
        | exact (hs.rops _ _ ‹s.rops.get? _ = some _›).2 vt hvt
        | (cases hvt; vk_pair))))

set_option hygiene false in
macro "vk_rops" : tactic => `(tactic| (
  intro K rd hrd
  try simp only [AMap.get?_put, AMap.get?_del] at hrd
  repeat' (split at hrd)
  all_goals first
    | exact hs.rops _ _ hrd
    | (cases hrd; done)
    | (refine hs.rops K rd (SCF.r ?_ K rd hrd); assumption)
    | (cases hrd; exact ⟨by vk_rdf, by vk_rdf⟩)))

set_option hygiene false in
macro "vk_wops" : tactic => `(tactic| (
  intro K w hw
  try simp only [AMap.get?_put, AMap.get?_del] at hw
  repeat' (split at hw)
  all_goals first
    | exact hs.wops _ _ hw
    | (cases hw; done)
    | (cases hw; have hold := hs.wops _ _ ‹s.wops.get? _ = some _›
       exact ⟨hold.1, hold.2.1, hold.2.2.1, hold.2.2.2⟩)
    | (cases hw; refine ⟨rfl, rfl, fun _ => rfl, fun wt hwt => by cases hwt⟩)))

set_option hygiene false in
/-- The whole `VS Q s' ∧ VO Q o` goal for a handler that keeps the records. -/
macro "vk_comp" : tactic => `(tactic| (first
    | (vk_pair; done)
    | (exact hs.prev; done)
    | (intro vt hvt; first | (exact hs.prev vt hvt; done) | (cases hvt; vk_pair; done))
    | (exact hs.inst; done)
    | (vk_inst; done)
    | (exact hs.rops; done)
    | (intro K rd h; refine hs.rops K rd (SCF.r ?_ K rd h); assumption)
    | (intro K rd h; exact hs.rops K rd (u6 K rd h))
    | (exact hs.wops; done)
    | (vk_out; done)
    | (vk_rops; done)
    | (vk_wops; done)))

set_option hygiene false in
macro "vk_fin" : tactic => `(tactic| (
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  all_goals vk_norm
  all_goals vk_comp))

section
variable {Q : w64 → model.Tag → Prop}

theorem startPhase1_v {s s' : RState} {q i b : w32} {ps : List Proposal} {cs : List Cmd}
    {o : List Out} (h : startPhase1 s q i b ps cs = .ok (s', o)) (hq0 : Q 0 model.tag0)
    (hs : VS Q s) : VS Q s' ∧ VO Q o := by
  unfold startPhase1 at h
  peel h
  all_goals (cases h; vk_fin)

theorem leaderCommit_v {s s' : RState} {q i : w32} {c : Copy} {lb : LB} {o : List Out}
    (h : leaderCommit s q i c lb = .ok (s', o)) (hq0 : Q 0 model.tag0) (hs : VS Q s)
    (hc : QV Q c.base) (hlb0 : ∀ ir, lb.recoveryInst = some ir → QV Q ir.base) :
    VS Q s' ∧ VO Q o := by
  unfold leaderCommit at h
  peel h
  all_goals (cases h; vk_fin)

set_option hygiene false in
macro "vk_lc" : tactic => `(tactic| (
  refine leaderCommit_v h hq0 ⟨?_, ?_, ?_, ?_, ?_⟩ ?_ (fun ir hir => ?_)
  all_goals vk_norm
  all_goals vk_comp))

set_option maxHeartbeats 4000000 in
theorem stepPreAccept_v {s s' : RState} {m : PreAcceptM} {o : List Out}
    (h : stepPreAccept s m = .ok (s', o)) (hq0 : Q 0 model.tag0) (hs : VS Q s) (hm : QV Q m.base) :
    VS Q s' ∧ VO Q o := by
  unfold stepPreAccept at h
  peel h
  all_goals (cases h; vk_fin)

theorem stepAccept_v {s s' : RState} {m : EAcceptM} {o : List Out}
    (h : stepAccept s m = .ok (s', o)) (hq0 : Q 0 model.tag0) (hs : VS Q s) (hm : QV Q m.base) :
    VS Q s' ∧ VO Q o := by
  unfold stepAccept at h
  peel h
  all_goals (cases h; vk_fin)

theorem stepCommit_v {s s' : RState} {m : ECommitM} {o : List Out}
    (h : stepCommit s m = .ok (s', o)) (hq0 : Q 0 model.tag0) (hs : VS Q s) (hm : QV Q m.base) :
    VS Q s' ∧ VO Q o := by
  unfold stepCommit at h
  peel h
  all_goals (cases h; vk_fin)

theorem stepPrepare_v {s s' : RState} {m : PrepareM} {o : List Out}
    (h : stepPrepare s m = .ok (s', o)) (hq0 : Q 0 model.tag0) (hs : VS Q s) :
    VS Q s' ∧ VO Q o := by
  unfold stepPrepare at h
  peel h
  all_goals (cases h)
  all_goals (try simp only [‹slt _ _ = true›, if_true] at *)
  all_goals (try simp only [‹¬slt _ _ = true›, if_false, Bool.false_eq_true] at *)
  all_goals vk_fin

set_option maxHeartbeats 4000000 in
theorem stepRecover_v {s s' : RState} {q i : w32} {o : List Out}
    (h : stepRecover s q i = .ok (s', o)) (hq0 : Q 0 model.tag0) (hs : VS Q s) :
    VS Q s' ∧ VO Q o := by
  unfold stepRecover at h
  peel h
  all_goals (cases h; vk_fin)

theorem handleExecuted_v {s s' : RState} {m : ExecutedM} {o : List Out}
    (h : handleExecuted s m = .ok (s', o)) (hq0 : Q 0 model.tag0) (hs : VS Q s) :
    VS Q s' ∧ VO Q o := by
  unfold handleExecuted at h
  peel h
  all_goals (cases h; vk_fin)

theorem stepPreAcceptReply_v {s s' : RState} {m : PreAcceptReplyM} {o : List Out}
    (h : stepPreAcceptReply s m = .ok (s', o)) (hq0 : Q 0 model.tag0) (hs : VS Q s)
    (hm : QV Q m.base) :
    VS Q s' ∧ VO Q o := by
  unfold stepPreAcceptReply at h
  peel h
  all_goals first
    | (cases h; vk_fin)
    | vk_lc

theorem stepPreAcceptOK_v {s s' : RState} {m : PreAcceptOKM} {o : List Out}
    (h : stepPreAcceptOK s m = .ok (s', o)) (hq0 : Q 0 model.tag0) (hs : VS Q s) :
    VS Q s' ∧ VO Q o := by
  unfold stepPreAcceptOK at h
  peel h
  all_goals first
    | (cases h; vk_fin)
    | vk_lc

theorem stepAcceptReply_v {s s' : RState} {m : AcceptReplyM} {o : List Out}
    (h : stepAcceptReply s m = .ok (s', o)) (hq0 : Q 0 model.tag0) (hs : VS Q s) :
    VS Q s' ∧ VO Q o := by
  unfold stepAcceptReply at h
  peel h
  all_goals first
    | (cases h; vk_fin)
    | vk_lc

set_option maxHeartbeats 4000000 in
theorem stepPrepareReply_v {s s' : RState} {m : PrepareReplyM} {o : List Out}
    (h : stepPrepareReply s m = .ok (s', o)) (hq0 : Q 0 model.tag0) (hs : VS Q s)
    (hm : QV Q m.base) : VS Q s' ∧ VO Q o := by
  unfold stepPrepareReply at h
  peel h
  all_goals first
    | (cases h; vk_fin)
    | (refine startPhase1_v h hq0 ⟨?_, ?_, ?_, ?_, ?_⟩
       all_goals vk_norm
       all_goals vk_comp)

theorem stepExecuteOverwrite_v {s s' : RState} {m : ExecuteOverwriteM} {o : List Out}
    (h : stepExecuteOverwrite s m = .ok (s', o)) (hq0 : Q 0 model.tag0) (hs : VS Q s)
    (hm : Q m.v m.t) : VS Q s' ∧ VO Q o := by
  unfold stepExecuteOverwrite at h
  peel h
  all_goals first
    | (cases h; vk_fin)
    | (refine handleExecuted_v h hq0 ⟨?_, ?_, ?_, ?_, ?_⟩
       all_goals vk_norm
       all_goals vk_comp)

/-- The source: an execution's result. -/
theorem stepExec_v {s s' : RState} {q i : w32} {o : List Out}
    (h : stepExec s q i = .ok (s', o)) (hq0 : Q 0 model.tag0) (hs : VS Q s)
    (hsrc : ∀ vt, execRes o = some vt → QV Q vt) : VS Q s' ∧ VO Q o := by
  have hp := stepExec_pc h
  unfold stepExec at h
  peel h
  all_goals (cases h)
  all_goals (try (obtain ⟨d, rfl⟩ := sendTo_some ‹sendTo _ _ = some _›))
  all_goals (refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals first
    | (intro vt hvt
       rcases hp.2.2 with ⟨-, hpv⟩ | ⟨vt', hv', hpv⟩
       · rw [hpv] at hvt; exact hs.prev _ hvt
       · rw [hpv] at hvt; cases hvt; exact hsrc _ hv')
    | exact VO.nil
    | (intro y hy; rw [List.mem_singleton.1 hy]; exact hsrc _ rfl)
    | (vk_norm; vk_comp)

theorem stepRead1_v {s s' : RState} {m : Read1ProxiedM} {o : List Out}
    (h : stepRead1 s m = .ok (s', o)) (hq0 : Q 0 model.tag0) (hs : VS Q s)
    (hm : QV Q m.vt ∧ QV Q m.d.vt) : VS Q s' ∧ VO Q o := by
  unfold stepRead1 at h
  peel h
  all_goals (cases h; vk_fin)

theorem stepRead2_v {s s' : RState} {m : Read2ProxiedM} {o : List Out}
    (h : stepRead2 s m = .ok (s', o)) (hq0 : Q 0 model.tag0) (hs : VS Q s)
    (hm : QV Q m.vt) : VS Q s' ∧ VO Q o := by
  unfold stepRead2 at h
  peel h
  all_goals (cases h; vk_fin)

theorem stepWrite2_v {s s' : RState} {m : Write2ProxiedM} {o : List Out}
    (h : stepWrite2 s m = .ok (s', o)) (hq0 : Q 0 model.tag0) (hs : VS Q s)
    (hm : QV Q m.vt) : VS Q s' ∧ VO Q o := by
  unfold stepWrite2 at h
  peel h
  all_goals (cases h; vk_fin)

theorem stepWrite1_v {s s' : RState} {m : Write1ProxiedM} {o : List Out}
    (h : stepWrite1 s m = .ok (s', o)) (hq0 : Q 0 model.tag0) (hs : VS Q s)
    (hm : sge m.d.key 0 = true → QV Q m.d.vt) : VS Q s' ∧ VO Q o := by
  unfold stepWrite1 at h
  peel h
  all_goals (cases h)
  all_goals (try have hm := hm ‹_›)
  all_goals vk_fin

set_option maxHeartbeats 2000000 in
theorem stepRead1Reply_v {s s' : RState} {m : Read1ReplyM} {o : List Out}
    (h : stepRead1Reply s m = .ok (s', o)) (hq0 : Q 0 model.tag0) (hs : VS Q s)
    (hm : QV Q m.vt) : VS Q s' ∧ VO Q o := by
  unfold stepRead1Reply at h
  peel h
  all_goals (cases h; refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals vk_norm
  all_goals vk_comp

theorem stepRead2Reply_v {s s' : RState} {m : Read2ReplyM} {o : List Out}
    (h : stepRead2Reply s m = .ok (s', o)) (hq0 : Q 0 model.tag0) (hs : VS Q s) :
    VS Q s' ∧ VO Q o := by
  unfold stepRead2Reply at h
  peel h
  all_goals (cases h; vk_fin)

theorem stepWrite2Reply_v {s s' : RState} {m : Write2ReplyM} {o : List Out}
    (h : stepWrite2Reply s m = .ok (s', o)) (hq0 : Q 0 model.tag0) (hs : VS Q s) :
    VS Q s' ∧ VO Q o := by
  unfold stepWrite2Reply at h
  peel h
  all_goals (cases h; refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals vk_norm
  all_goals first
    | vk_comp
    | exact VO.append (shortCircuit_ite_v ‹(if _ then shortCircuit _ _ _ _ else some _) = some _›).2 VO.ext

theorem stepClientWrite_v {s s' : RState} {rid cid : w32} {k v : w64} {d : Dep} {o : List Out}
    (h : stepClientWrite s rid cid k v d = .ok (s', o)) (hq0 : Q 0 model.tag0) (hs : VS Q s) :
    VS Q s' ∧ VO Q o := by
  unfold stepClientWrite at h
  peel h
  all_goals (cases h; refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals vk_norm
  all_goals first
    | vk_comp
    | (apply VO.ofMapSendTo ‹List.mapM _ _ = some _›
       intro hk
       exfalso
       simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, sge, sle, slt,
         decide_eq_true_eq] at *
       omega)

theorem stepClientRead_v {s s' : RState} {rid cid : w32} {k : w64} {d : Dep} {o : List Out}
    (h : stepClientRead s rid cid k d = .ok (s', o)) (hq0 : Q 0 model.tag0) (hs : VS Q s) :
    VS Q s' ∧ VO Q o := by
  unfold stepClientRead at h
  peel h
  cases h
  have hx := ‹forIn _ _ _ = Except.ok s'›
  have hP : s'.val = s.val ∧ s'.tag = s.tag ∧ s'.prevValTag = s.prevValTag ∧ s'.inst = s.inst ∧
      s'.wops = s.wops ∧ ∀ K rd, s'.rops.get? K = some rd → VRd Q rd := by
    refine forIn_exc_inv _ _ _ (fun x : RState => x.val = s.val ∧ x.tag = s.tag ∧
      x.prevValTag = s.prevValTag ∧ x.inst = s.inst ∧ x.wops = s.wops ∧
      ∀ K rd, x.rops.get? K = some rd → VRd Q rd) ?_ ?_ _ hx
    · refine ⟨rfl, rfl, rfl, rfl, rfl, fun K rd hrd => ?_⟩
      simp only [AMap.get?_put] at hrd
      split at hrd
      · cases hrd
        unfold VRd
        exact ⟨fun vt h => by simp at h, fun vt h => by simp at h⟩
      · exact hs.rops K rd hrd
    intro a b st hb hf
    peel hf
    all_goals (cases hf; exact hb)
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hP
  refine ⟨⟨by rw [e1, e2]; exact hs.store, by rw [e3]; exact hs.prev, by rw [e4]; exact hs.inst,
    e6, by rw [e5]; exact hs.wops⟩, ?_⟩
  apply VO.ofMapSendPeer ‹List.mapM _ _ = some o›
  simp only [VM, QV, RState.storeVT]
  exact ⟨by rw [e1, e2]; exact hs.store, by simpa [dep0, vt0] using hq0⟩

theorem get?_put_self {V : Type} (m : model.AMap 64 V) (k : BitVec 64) (v : V) :
    (m.put k v).get? k = some v := by rw [AMap.get?_put, if_pos rfl]

/-- A hypothesis kept out of `simp`'s way. -/
def Keep (p : Prop) : Prop := p

theorem sge_m1 : sge (-1 : w64) 0 = false := by decide
theorem sge_0_two : sge (0 : w64) (NHALF + 1) = false := by decide
theorem sge_of_m1 {x : w64} (h : x = -1) : sge x 0 = false := by rw [h]; exact sge_m1
theorem sge_of_0 {x : w64} (h : x = 0) : sge x (NHALF + 1) = false := by rw [h]; exact sge_0_two

set_option maxHeartbeats 4000000 in
/-- The source of write pairs: the `Write1Reply` handler (its fast path never fires: the record
has `numWrite1Applies = 0`, and the reply's value is `-1`). -/
theorem stepWrite1Reply_v {s s' : RState} {m : Write1ReplyM} {o : List Out}
    (h : stepWrite1Reply s m = .ok (s', o)) (hq0 : Q 0 model.tag0) (hs : VS Q s)
    (hm : m.vt.v = -1)
    (hsrc : ∀ K w w', s.wops.get? K = some w → w.writeTag = none → s'.wops.get? K = some w' →
      ∀ wt, w'.writeTag = some wt → Q w'.writeValue wt) : VS Q s' ∧ VO Q o := by
  unfold stepWrite1Reply at h
  peel h
  all_goals (cases h)
  all_goals (try (refine (fun hw0 => ?_) (hs.wops _ _ ‹s.wops.get? _ = some _›)
                  obtain ⟨hw1, hw2, hw3, hw4⟩ := hw0
                  have e1 := sge_of_m1 hm
                  have e2 := sge_of_m1 hw2
                  have e3 := sge_of_0 hw1
                  simp only [e1, e2, e3, sge_0_two, Bool.false_eq_true, Bool.and_false,
                    if_false] at *))
  all_goals (refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
  all_goals vk_norm
  all_goals first
    | vk_comp
    | (intro K w hw
       simp only [AMap.get?_put] at hw
       split at hw
       · cases hw
         first
         | exact ⟨rfl, hm, hw3, hw4⟩
         | exact ⟨hw1, hw2, hw3, hw4⟩
         | exact ⟨rfl, hw2, hw3, hw4⟩
         | (refine ⟨?_, ?_, fun h => by simp at h, fun wt hwt => ?_⟩
            · first | rfl | exact hw1
            · first | exact hm | exact hw2
            · refine hsrc _ _ _ ‹s.wops.get? _ = some _› (hw3 (by simpa using ‹(!_) = true›)) ?_ wt hwt
              simp [AMap.get?_put])
       · exact hs.wops _ _ hw)
    | (apply VO.ofMapSendTo ‹List.mapM _ _ = some _›
       simp only [VM, QV]
       exact hsrc _ _ _ ‹s.wops.get? _ = some _› (hw3 (by simpa using ‹(!_) = true›))
         (get?_put_self _ _ _) _ rfl)


end

/-- **L3 per step.** -/
theorem step_v {Q : w64 → model.Tag → Prop} {r : Fin 3} {s s' : RState} {e : Ev} {o : List Out}
    (h : stepR r s e = .ok (s', o)) (hq0 : Q 0 model.tag0) (hs : VS Q s)
    (hm : ∀ m, e.recv = some m → VM Q m)
    (hsE : ∀ q i, e = .exec q i → ∀ vt, execRes o = some vt → QV Q vt)
    (hsW : ∀ m, e = .msg (.write1Reply m) → ∀ K w w', s.wops.get? K = some w →
      w.writeTag = none → s'.wops.get? K = some w' → ∀ wt, w'.writeTag = some wt →
      Q w'.writeValue wt) :
    VS Q s' ∧ VO Q o := by
  cases e with
  | read => exact stepClientRead_v h hq0 hs
  | write => exact stepClientWrite_v h hq0 hs
  | rmw rid cid k d a b =>
    change stepClientRMW s rid cid k d a b = _ at h
    unfold stepClientRMW at h
    peel h
    obtain ⟨-, -, h⟩ := handlePropose_ok h; unfold handleProposeBody at h
    exact startPhase1_v h hq0 ⟨hs.store, hs.prev, hs.inst, hs.rops, hs.wops⟩
  | forceWrite => cases h; exact ⟨hs, VO.nil⟩
  | recover => exact stepRecover_v h hq0 hs
  | exec q i => exact stepExec_v h hq0 hs (hsE q i rfl)
  | msg m =>
    have hm' := hm m rfl
    cases m with
    | read1 => exact stepRead1_v h hq0 hs hm'
    | read2 => exact stepRead2_v h hq0 hs hm'
    | write1 => exact stepWrite1_v h hq0 hs hm'
    | write2 => exact stepWrite2_v h hq0 hs hm'
    | read1Reply => exact stepRead1Reply_v h hq0 hs hm'
    | read2Reply => exact stepRead2Reply_v h hq0 hs
    | write1Reply m => exact stepWrite1Reply_v h hq0 hs hm' (hsW m rfl)
    | write2Reply => exact stepWrite2Reply_v h hq0 hs
    | prepare => exact stepPrepare_v h hq0 hs
    | preAccept => exact stepPreAccept_v h hq0 hs hm'
    | accept => exact stepAccept_v h hq0 hs hm'
    | commit => exact stepCommit_v h hq0 hs hm'
    | prepareReply => exact stepPrepareReply_v h hq0 hs hm'
    | preAcceptReply => exact stepPreAcceptReply_v h hq0 hs hm'
    | preAcceptOK => exact stepPreAcceptOK_v h hq0 hs
    | acceptReply => exact stepAcceptReply_v h hq0 hs
    | executed => exact handleExecuted_v h hq0 hs
    | executeOverwrite => exact stepExecuteOverwrite_v h hq0 hs hm'

end Perennial.gryff.pure
