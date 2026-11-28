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
one's (256·(t1 − t0) + 1)-th; `nonissues/etcd-request-id-restart-reuse.md`). The model assumes it
(`assume`, which does not return when false), following the approach of the SOSP'26 paper for this
limit (`/shared/grove-paper/sosp26/case.tex`, `rwmutex.tex`).

* An entry `id ↦ some g`: the generator at address `g`, of the machine's current incarnation (since
  its last crash), issued `id`; `id ↦ none`: a generator of an earlier incarnation issued it.
* `"Issue"` of `(id, g)`, an id and the address of the generator that computed it: `true` if no
  other generator issued `id` (the record has no entry for it, or `some g`), with `id ↦ some g`
  recorded; `false` (record unchanged) if another generator did, of this incarnation or an earlier
  one.
* It does not fail and does not change the heap.
* **A crash** of the machine (a process's restart is one) keeps every entry, as an earlier
  incarnation's (`idIssueCrash`: `some g` becomes `none`): a generator of the restarted process may
  issue none of the ids issued before, whatever its address (the heap is new, so it may get a
  stopped generator's address: keyed by the address alone, as until etcd-dist D4b, 2026-11-24, the
  record took the two for one and admitted a reissue across a real crash,
  `nonissues/etcd-request-id-restart-reuse.md`). The assumption is the same as within one run, now
  across the machine's restarts: the wall clock does not step back across a restart, and the earlier
  generators issued at most 256 ids per millisecond since their start (and, from the timestamp's 40
  bits, a machine's generators started less than 2^40 ms, 34.8 years, apart).
  `examples/idissue/semantics/crash_keeps_record_test.go`.
* The extension's name is not a Go package's (as an extension's usually is, `CLAUDE.md`): it
  implements none; the record is model-only, and only the trusted `Next` calls it. It is per node
  (GooseLang's local state): generators on different nodes are told apart by their prefixes, proved
  (`examples/idissue/semantics/per_machine_test.go`).
* Any initial record (`ExtSemantics`'s default `initLocal`): a theorem holds from the empty one too.

The extension is the examples' one (it replaces `trivialExt`, which had no operations): a program
that never calls `"Issue"` sees GooseLang's semantics.
-/
module

public import Perennial.GooseLang.Lang

@[expose] public section

namespace Perennial

/-- The record: each issued id's generator (`some g`, of the machine's current incarnation), or
`none` (a generator of an earlier incarnation). -/
abbrev IdIssueState := GMap w64 (Option Loc)

instance : Inhabited IdIssueState := ⟨∅⟩

/-- The issue-record extension. No values of its own, no global state. -/
@[reducible] def idIssueExt : GooseExt where
  name := "go.etcd.io/etcd/pkg/v3/idutil.issue"
  Val := Empty
  LocalState := IdIssueState
  GlobalState := Unit

section idIssue
variable [GooseExts] [GoGlobalContext]

/-- Whether the generator `g` may issue `id`: no other generator has, of this incarnation or an
earlier one. -/
def idIssueOk (M : IdIssueState) (id : w64) (g : Loc) : Bool :=
  match M !! id with
  | none => true
  | some (some g') => decide (g' = g)
  | some none => false

/-- The record after an `"Issue"` of `id` by `g`. -/
def idIssueNext (M : IdIssueState) (id : w64) (g : Loc) : IdIssueState :=
  if idIssueOk M id g then M.insert id (some g) else M

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

/-- The record after a crash: every entry kept, as an earlier incarnation's. -/
def idIssueCrash (M : IdIssueState) : IdIssueState := GMap.fmap (fun _ => (none : Option Loc)) M

/-- A crash keeps the record, every entry an earlier incarnation's (`idIssueCrash`). -/
instance idIssue_semantics : ExtSemantics idIssueExt where
  step := fun _ => IdIssueStep
  crash M M' := M' = idIssueCrash M

end Perennial
