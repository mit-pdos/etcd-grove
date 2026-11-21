/- Looking up the term of an index in a Ready batch's immutable replay log. -/
module
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply

@[expose] public section
noncomputable section
namespace Perennial
namespace EtcdGrove
open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- A batch may retain the beginning of a run below its delivered prefix.
Only the first run ending at or after the requested index can supply its term. -/
def replayRunAt (runs : List replayTermRun) (index : w64) : Option replayTermRun :=
  runs.find? (fun run => decide (uint.nat index ≤ uint.nat run.last'))

theorem replayRunAt_after (runs : List replayTermRun) (applied index : w64)
    (h : uint.nat applied < uint.nat index) :
    replayRunAt (runs.dropWhile (fun run => decide (uint.nat run.last' ≤ uint.nat applied))) index =
      replayRunAt runs index := by
  induction runs with
  | nil => rfl
  | cons run rest ih =>
    by_cases hd : uint.nat run.last' ≤ uint.nat applied
    · have hl : ¬uint.nat index ≤ uint.nat run.last' := by omega
      simpa [List.dropWhile, replayRunAt, List.find?, hd, hl] using ih
    · simp [List.dropWhile, hd]

/-- Joining two adjacent runs with the same term preserves the value read by
`termAt`. An earlier run in the same immutable Ready still wins the lookup. -/
theorem replayRunAt_coalesce (prior : List replayTermRun) (left right : replayTermRun)
    (index : w64) (hends : uint.nat left.last' ≤ uint.nat right.last')
    (hterm : left.term' = right.term') :
    (replayRunAt (prior ++ [left, right]) index).map (·.term') =
      (replayRunAt (prior ++ [{ right with first' := left.first' }]) index).map (·.term') := by
  induction prior with
  | nil =>
    by_cases hl : uint.nat index ≤ uint.nat left.last'
    · have hr := Nat.le_trans hl hends
      simp [replayRunAt, List.find?, hl, hr, hterm]
    · by_cases hr : uint.nat index ≤ uint.nat right.last' <;>
        simp [replayRunAt, List.find?, hl, hr]
  | cons head tail ih =>
    by_cases hh : uint.nat index ≤ uint.nat head.last' <;>
      simp [replayRunAt, List.find?, hh] at ih ⊢ <;> assumption

/-- Replacing an uncommitted suffix can split a run. Its retained part still
answers every earlier index that used to select that run. -/
theorem replayRunAt_clip (prior oldTail newTail : List replayTermRun) (run : replayTermRun)
    (first index : w64) (h : uint.nat index < uint.nat first)
    (hend : uint.nat first ≤ uint.nat run.last') :
    (replayRunAt (prior ++ run :: oldTail) index).map (·.term') =
      (replayRunAt (prior ++ { run with last' := first - W64 1 } :: newTail) index).map
        (·.term') := by
  induction prior with
  | nil =>
    have hold : uint.nat index ≤ uint.nat run.last' := by omega
    have hclip : uint.nat index ≤ uint.nat (first - W64 1) := by word
    simp only [List.nil_append, replayRunAt, List.find?, hold, hclip, decide_true, Option.map_some]
  | cons head tail ih =>
    by_cases hh : uint.nat index ≤ uint.nat head.last' <;>
      simp [replayRunAt, List.find?, hh] at ih ⊢ <;> assumption

abbrev replayTerms.termAt.spec : Prop :=
  ∀ (r : GoSlice) (runs : List replayTermRun) (index : w64) (run : replayTermRun),
  replayRunAt runs index = some run →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ r ↦*□ runs }}
    (App (Val (r @!! replayTerms.ty @!! go!"termAt")) (Val #index))
  {{ RET #run.term'; True }}

end EtcdGrove
end Perennial
