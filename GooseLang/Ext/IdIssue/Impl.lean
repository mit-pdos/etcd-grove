/-
The request ids' issue record, a GooseLang extension [Trusted definitions!] (the restart plan's R2c
stage 2, 2026-11-02, `notes/restart-plan.md`).

Model-only state: which generator issued each request id. Go has no such record. It exists so that
the trusted model of `idutil`'s `(*Generator).Next` (`TrustedCode/go_etcd_io/etcd/pkg/v3/idutil.lean`)
can assume what etcd's code relies on and does not check: two generators never issue one id. A
member restarted under its old 16-bit prefix starts a second generator of that prefix, from the wall
clock, while its stopped incarnation's in-flight handlers may still call the first one's `Next`. Their
ids are distinct only if the clock does not step back and the first generator, started at millisecond
t0, issues in all at most 256·(t1 − t0) ids, t1 the second one's start (its first id is the first
one's (256·(t1 − t0) + 1)-th; `issues/etcd-request-id-restart-reuse.md`). The model assumes it
(`assume`, which does not return when false), following the approach of the SOSP'26 paper for this
limit (`/shared/grove-paper/sosp26/case.tex`, `rwmutex.tex`).

* `"Issue"` of `(id, g)`, an id and the address of the generator that computed it: `true` if no
  other generator issued `id` (the record has no entry for it, or `g`'s), with `id ↦ g` recorded;
  `false` (record unchanged) if another generator did.
* It does not fail and does not change the heap. Crashes keep the record (there are none: the
  examples' theorems are crash-free). If crashes are ever modeled, a generator allocated after one
  may get a stopped one's address, and the record would take the two for one: still sound (it
  excludes fewer executions), but `Next`'s proof would then need the record cleared or keyed by
  something else.
* The extension's name is not a Go package's (as an extension's usually is, `CLAUDE.md`): it
  implements none; the record is model-only, and only the trusted `Next` calls it. It is per node
  (GooseLang's local state): generators on different nodes are told apart by their prefixes, proved.

The extension is the examples' one (it replaces `trivialExt`, which had no operations): a program
that never calls `"Issue"` sees GooseLang's semantics.
-/
module

public import Perennial.GooseLang.Lang

@[expose] public section

namespace Perennial

/-- The record: each issued id's generator. -/
abbrev IdIssueState := GMap w64 Loc

instance : Inhabited IdIssueState := ⟨∅⟩

/-- The issue-record extension. No values of its own, no global state. -/
@[reducible] def idIssueExt : GooseExt where
  name := "go.etcd.io/etcd/pkg/v3/idutil.issue"
  Val := Empty
  LocalState := IdIssueState
  GlobalState := Unit

section idIssue
variable [GooseExts] [GoGlobalContext]

/-- Whether the generator `g` may issue `id`: no other generator has. -/
def idIssueOk (M : IdIssueState) (id : w64) (g : Loc) : Bool :=
  match M !! id with
  | none => true
  | some g' => decide (g' = g)

/-- The record after an `"Issue"` of `id` by `g`. -/
def idIssueNext (M : IdIssueState) (id : w64) (g : Loc) : IdIssueState :=
  if idIssueOk M id g then M.insert id g else M

/-- The step relation. -/
def IdIssueStep (op : String) (v : val) (h : GMap Loc (NonAtomic val)) (M : IdIssueState)
    (_gs : Unit) (e' : Expr) (h' : GMap Loc (NonAtomic val)) (M' : IdIssueState) (_gs' : Unit) :
    Prop :=
  h' = h ∧
  match op with
  | "Issue" => ∃ (id : w64) (g : Loc),
      v = PairV (#id) (#g) ∧ e' = Val (#(idIssueOk M id g)) ∧ M' = idIssueNext M id g
  | _ => False

end idIssue

/-- A crash keeps the record. -/
instance idIssue_semantics : ExtSemantics idIssueExt where
  step := IdIssueStep
  crash M M' := M' = M

end Perennial
