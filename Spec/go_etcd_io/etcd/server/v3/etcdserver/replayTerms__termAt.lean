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

abbrev replayTerms.termAt.spec : Prop :=
  ∀ (r : GoSlice) (runs : List replayTermRun) (index : w64) (run : replayTermRun),
  replayRunAt runs index = some run →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ r ↦*□ runs }}
    (App (Val (r @!! replayTerms.ty @!! go!"termAt")) (Val #index))
  {{ RET #run.term'; True }}

end EtcdGrove
end Perennial
