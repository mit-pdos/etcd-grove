/-
# A `ConfRule` as the protocol's decoder (2026-10-28, stages U1, U6m)

The bridge from the API's `ConfRule` (`ConfRule.lean`) to the protocol's decision decoder (`CCDec`,
`Protocol/CfgOverlap.lean`): `ConfRule.toDec r c0` decides a conf entry after a prefix by the rule at
the membership the prefix folds to -- the rule's change applied (as `AsV2` makes it), its `none` a
rejection (`CCDecision.reject`). `cfgFold_toDec`: the protocol's fold of a log is the API's
`Membership.fold` of the log as a client sees it, from a valid `c0` (for any rule: a change keeps a
membership valid). Internal: it reads the sealed `Membership.Valid`/`applyChange`.
-/
module

public import Proof.go_etcd_io.raft.v3.ConfRule
public import Proof.go_etcd_io.raft.v3.InvApiDyn
import all Proof.go_etcd_io.raft.v3.InvNode

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3 ApiImpl

section pure
variable [GooseExts]

/-- **A rule as the protocol's decoder**: after the prefix `pre`, at the membership it folds to, the
rule's change applied (as `AsV2` makes it), its `none` a rejection; `none` where the prefix has no
membership. -/
def ConfRule.toDec (r : ConfRule) (c0 : Membership) : CCDec := fun pre e =>
  (Membership.fold r c0 (strip pre)).map fun m =>
    match r (strip pre) m (LogEntry.ofEntryM e) with
    | none => .reject
    | some o => .apply (ccV2Of o)

/-- The decision at a prefix with a membership. -/
theorem ConfRule.toDec_at (r : ConfRule) (c0 m : Membership) (pre : List EntryM) (e : EntryM)
    (h : Membership.fold r c0 (strip pre) = some m) :
    r.toDec c0 pre e = some (match r (strip pre) m (LogEntry.ofEntryM e) with
      | none => .reject
      | some o => .apply (ccV2Of o)) := by
  unfold ConfRule.toDec; rw [h]; rfl

/-- The rule rejects the entry exactly where the decoder does. -/
theorem ConfRule.toDec_reject (r : ConfRule) (c0 m : Membership) (pre : List EntryM) (e : EntryM)
    (h : Membership.fold r c0 (strip pre) = some m)
    (hr : r (strip pre) m (LogEntry.ofEntryM e) = none) :
    r.toDec c0 pre e = some .reject := by
  rw [r.toDec_at c0 m pre e h, hr]

theorem strip_snoc (pre : List EntryM) (e : EntryM) :
    strip (pre ++ [e]) = strip pre ++ [LogEntry.ofEntryM e] := by
  unfold strip; rw [List.map_append]; rfl

/-- **The protocol's fold is the API's**: from a valid `c0`, `cfgFold` of the rule's decoder over a
log is `Membership.fold` of the log as a client sees it, each membership as its canonical state. -/
theorem cfgFold_toDec (r : ConfRule) (c0 : Membership) (h0 : c0.Valid) (L : List EntryM) :
    cfgFold (r.toDec c0) (stOf c0) L = (Membership.fold r c0 (strip L)).map stOf := by
  suffices H : ∀ (pre : List EntryM) (m : Membership), m.Valid →
      Membership.fold r c0 (strip pre) = some m →
      cfgFoldFrom (r.toDec c0) pre (stOf m) L
        = (Membership.foldFrom r (strip pre) m (strip L)).map stOf from H [] c0 h0 rfl
  induction L with
  | nil => intro pre m _ _; rfl
  | cons e L ih =>
    intro pre m hm hf
    have hv : memValid m := hm
    have hstrip : strip (e :: L) = LogEntry.ofEntryM e :: strip L := rfl
    rw [hstrip]
    simp only [cfgFoldFrom, Membership.foldFrom]
    have hconf : IsConfEnt e ↔ (LogEntry.ofEntryM e).isConfChange := Iff.rfl
    by_cases hc : IsConfEnt e
    · have hc' := hconf.1 hc
      cases ho : r (strip pre) m (LogEntry.ofEntryM e) with
      | none =>
        have hst : entStep (r.toDec c0) pre (stOf m) e = some (stOf m) := by
          unfold entStep; rw [ite_eq_left hc, r.toDec_at c0 m pre e hf, ho]; rfl
        have hfs : Membership.foldStep r (strip pre) m (LogEntry.ofEntryM e) = some m := by
          unfold Membership.foldStep; rw [ite_eq_left hc', ho]
        rw [hst, hfs]
        simp only [Option.bind_some]
        rw [← strip_snoc]
        apply ih (pre ++ [e]) m hm
        rw [strip_snoc, Membership.fold_snoc_conf r c0 m _ _ hc' hf, ho]
      | some o =>
        have hst : entStep (r.toDec c0) pre (stOf m) e = ccStepB (ccV2Of o) (stOf m) := by
          unfold entStep; rw [ite_eq_left hc, r.toDec_at c0 m pre e hf, ho]; rfl
        have hfs : Membership.foldStep r (strip pre) m (LogEntry.ofEntryM e)
            = Membership.applyChange o m := by
          unfold Membership.foldStep; rw [ite_eq_left hc', ho]
        rw [hst, hfs]
        cases ha : Membership.applyChange o m with
        | none =>
          have : ccStepB (ccV2Of o) (stOf m) = none := by
            have ha' : memApply o m = none := ha
            unfold memApply at ha'
            cases hs : ccStepB (ccV2Of o) (stOf m) with
            | none => rfl
            | some _ => rw [hs] at ha'; cases ha'
          rw [this]; rfl
        | some m' =>
          have ha' : memApply o m = some m' := ha
          obtain ⟨hs, -⟩ := memApply_some hv.2 ha'
          rw [hs]
          simp only [Option.bind_some]
          rw [← strip_snoc]
          apply ih (pre ++ [e]) m' (memApply_valid o m m' hv ha')
          rw [strip_snoc, Membership.fold_snoc_conf r c0 m _ _ hc' hf, ho]
          exact ha
    · have hc' : ¬ (LogEntry.ofEntryM e).isConfChange := fun h => hc (hconf.2 h)
      rw [entStep_not_conf _ _ _ _ hc]
      simp only [Membership.foldStep, ite_eq_right hc', Option.bind_some]
      rw [← strip_snoc]
      apply ih (pre ++ [e]) m hm
      rw [strip_snoc, Membership.fold_snoc_normal r c0 _ _ hc', hf]

end pure

end EtcdGrove
end Perennial
