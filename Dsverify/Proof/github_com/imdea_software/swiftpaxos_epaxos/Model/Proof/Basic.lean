/-
Basic facts for the model's invariant proofs: `upd`, and the effect of `Sys.applyStep` (a
replica's state replaced, its outputs applied in order) field by field.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.InvDefs

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

@[simp] theorem upd_same {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) :
    upd f a b a = b := by simp [upd]

theorem upd_apply {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) (a' : α) :
    upd f a b a' = if a' = a then b else f a' := rfl

@[simp] theorem upd_other {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) (a' : α)
    (h : a' ≠ a) : upd f a b a' = f a' := by simp [upd, h]

@[simp] theorem upd_upd_same {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b c : β) :
    upd (upd f a b) a c = upd f a c := by
  funext a'; by_cases h : a' = a <;> simp [upd, h]

@[simp] theorem upd_eta {α β : Type} [DecidableEq α] (f : α → β) (a : α) :
    upd f a (f a) = f := by
  funext a'; by_cases h : a' = a <;> simp [upd, h]

/-! ## Outputs -/

/-- The history event an output logs (a send logs `Event.sent`). -/
def Out.hev : Out → Option Event
  | .send to m => some (.sent to m)
  | .ev e => some e
  | _ => none

/-- The message an output sends directly to `to`. -/
def Out.sendTo (to : Nat) : Out → Option Msg
  | .send t m => if t = to then some m else none
  | _ => none

/-- The proposal an output re-proposes. -/
def Out.reprop : Out → Option Proposal
  | .repropose p => some p
  | _ => none

/-- The pending broadcast after outputs `os`, from `p`. -/
def pendFold (os : List Out) (p : Option Bcast) : Option Bcast :=
  os.foldl (fun acc o => match o with | .bcast b => b.norm | _ => acc) p

theorem pendOf_eq (os : List Out) : pendOf os = pendFold os none := rfl

namespace Sys

theorem foldl_emit_rep (os : List Out) (S : Sys) (i : Nat) :
    (os.foldl (fun S o => S.emit i o) S).rep = S.rep := by
  induction os generalizing S with
  | nil => rfl
  | cons o os ih => rw [List.foldl_cons, ih]; cases o <;> rfl

theorem foldl_emit_sent (os : List Out) (S : Sys) (i : Nat) :
    (os.foldl (fun S o => S.emit i o) S).sent = S.sent := by
  induction os generalizing S with
  | nil => rfl
  | cons o os ih => rw [List.foldl_cons, ih]; cases o <;> rfl

theorem foldl_emit_delivered (os : List Out) (S : Sys) (i : Nat) :
    (os.foldl (fun S o => S.emit i o) S).delivered = S.delivered := by
  induction os generalizing S with
  | nil => rfl
  | cons o os ih => rw [List.foldl_cons, ih]; cases o <;> rfl

theorem foldl_emit_ops (os : List Out) (S : Sys) (i : Nat) :
    (os.foldl (fun S o => S.emit i o) S).ops = S.ops := by
  induction os generalizing S with
  | nil => rfl
  | cons o os ih => rw [List.foldl_cons, ih]; cases o <;> rfl

theorem foldl_emit_owner (os : List Out) (S : Sys) (i : Nat) :
    (os.foldl (fun S o => S.emit i o) S).owner = S.owner := by
  induction os generalizing S with
  | nil => rfl
  | cons o os ih => rw [List.foldl_cons, ih]; cases o <;> rfl

theorem foldl_emit_execLog (os : List Out) (S : Sys) (i : Nat) :
    (os.foldl (fun S o => S.emit i o) S).execLog = S.execLog := by
  induction os generalizing S with
  | nil => rfl
  | cons o os ih => rw [List.foldl_cons, ih]; cases o <;> rfl

theorem foldl_emit_execCur (os : List Out) (S : Sys) (i : Nat) :
    (os.foldl (fun S o => S.emit i o) S).execCur = S.execCur := by
  induction os generalizing S with
  | nil => rfl
  | cons o os ih => rw [List.foldl_cons, ih]; cases o <;> rfl

theorem foldl_emit_execIdx (os : List Out) (S : Sys) (i : Nat) :
    (os.foldl (fun S o => S.emit i o) S).execIdx = S.execIdx := by
  induction os generalizing S with
  | nil => rfl
  | cons o os ih => rw [List.foldl_cons, ih]; cases o <;> rfl

theorem foldl_emit_gexec (os : List Out) (S : Sys) (i : Nat) :
    (os.foldl (fun S o => S.emit i o) S).gexec = S.gexec := by
  induction os generalizing S with
  | nil => rfl
  | cons o os ih => rw [List.foldl_cons, ih]; cases o <;> rfl

theorem foldl_emit_fired (os : List Out) (S : Sys) (i : Nat) :
    (os.foldl (fun S o => S.emit i o) S).fired = S.fired := by
  induction os generalizing S with
  | nil => rfl
  | cons o os ih => rw [List.foldl_cons, ih]; cases o <;> rfl

theorem foldl_emit_hist (os : List Out) (S : Sys) (i : Nat) :
    (os.foldl (fun S o => S.emit i o) S).hist =
      S.hist ++ os.filterMap (fun o => (Out.hev o).map (fun e => (i, e))) := by
  induction os generalizing S with
  | nil => simp
  | cons o os ih =>
    rw [List.foldl_cons, ih]; cases o <;> simp [Sys.emit, Out.hev, List.filterMap_cons]

theorem foldl_emit_outbox (os : List Out) (S : Sys) (i fr to : Nat) :
    (os.foldl (fun S o => S.emit i o) S).outbox fr to =
      S.outbox fr to ++ (if fr = i then os.filterMap (Out.sendTo to) else []) := by
  induction os generalizing S with
  | nil => by_cases h : fr = i <;> simp [h]
  | cons o os ih =>
    rw [List.foldl_cons, ih]
    cases o with
    | send t m =>
      by_cases h : fr = i
      · subst h; by_cases ht : to = t
        · subst ht; simp [Sys.emit, Out.sendTo]
        · simp [Sys.emit, Out.sendTo, upd_apply, ht, List.filterMap, Ne.symm ht]
      · simp [Sys.emit, upd_apply, h]
    | _ => by_cases h : fr = i <;> simp [Sys.emit, Out.sendTo, h, List.filterMap]

theorem foldl_emit_pending (os : List Out) (S : Sys) (i fr : Nat) :
    (os.foldl (fun S o => S.emit i o) S).pending fr =
      if fr = i then pendFold os (S.pending i) else S.pending fr := by
  induction os generalizing S with
  | nil => by_cases h : fr = i <;> simp [h, pendFold]
  | cons o os ih =>
    rw [List.foldl_cons, ih]
    cases o with
    | bcast b => by_cases h : fr = i <;> simp [Sys.emit, pendFold, h, upd_apply]
    | _ => by_cases h : fr = i <;> simp [Sys.emit, pendFold, h]

theorem foldl_emit_proposeChan (os : List Out) (S : Sys) (i fr : Nat) :
    (os.foldl (fun S o => S.emit i o) S).proposeChan fr =
      S.proposeChan fr ++ (if fr = i then os.filterMap Out.reprop else []) := by
  induction os generalizing S with
  | nil => by_cases h : fr = i <;> simp [h]
  | cons o os ih =>
    rw [List.foldl_cons, ih]
    cases o with
    | repropose p => by_cases h : fr = i <;> simp [Sys.emit, Out.reprop, h, upd_apply]
    | _ => by_cases h : fr = i <;> simp [Sys.emit, Out.reprop, h, List.filterMap]

/-! ## `applyStep`, field by field -/

section
variable (S : Sys) (i : Nat) (σ : RState) (os : List Out)

@[simp] theorem applyStep_rep : (S.applyStep i (σ, os)).rep = upd S.rep i σ := by
  simp [applyStep, foldl_emit_rep]
@[simp] theorem applyStep_sent : (S.applyStep i (σ, os)).sent = S.sent := by
  simp [applyStep, foldl_emit_sent]
@[simp] theorem applyStep_delivered : (S.applyStep i (σ, os)).delivered = S.delivered := by
  simp [applyStep, foldl_emit_delivered]
@[simp] theorem applyStep_ops : (S.applyStep i (σ, os)).ops = S.ops := by
  simp [applyStep, foldl_emit_ops]
@[simp] theorem applyStep_owner : (S.applyStep i (σ, os)).owner = S.owner := by
  simp [applyStep, foldl_emit_owner]
@[simp] theorem applyStep_execLog : (S.applyStep i (σ, os)).execLog = S.execLog := by
  simp [applyStep, foldl_emit_execLog]
@[simp] theorem applyStep_execCur : (S.applyStep i (σ, os)).execCur = S.execCur := by
  simp [applyStep, foldl_emit_execCur]
@[simp] theorem applyStep_execIdx : (S.applyStep i (σ, os)).execIdx = S.execIdx := by
  simp [applyStep, foldl_emit_execIdx]
@[simp] theorem applyStep_gexec : (S.applyStep i (σ, os)).gexec = S.gexec := by
  simp [applyStep, foldl_emit_gexec]
@[simp] theorem applyStep_fired : (S.applyStep i (σ, os)).fired = S.fired := by
  simp [applyStep, foldl_emit_fired]
@[simp] theorem applyStep_hist : (S.applyStep i (σ, os)).hist =
    S.hist ++ os.filterMap (fun o => (Out.hev o).map (fun e => (i, e))) := by
  simp [applyStep, foldl_emit_hist]
@[simp] theorem applyStep_outbox (fr to : Nat) : (S.applyStep i (σ, os)).outbox fr to =
    S.outbox fr to ++ (if fr = i then os.filterMap (Out.sendTo to) else []) := by
  simp [applyStep, foldl_emit_outbox]
@[simp] theorem applyStep_pending (fr : Nat) : (S.applyStep i (σ, os)).pending fr =
    if fr = i then pendFold os (S.pending i) else S.pending fr := by
  simp [applyStep, foldl_emit_pending]
@[simp] theorem applyStep_proposeChan (fr : Nat) : (S.applyStep i (σ, os)).proposeChan fr =
    S.proposeChan fr ++ (if fr = i then os.filterMap Out.reprop else []) := by
  simp [applyStep, foldl_emit_proposeChan]

end

end Sys

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
