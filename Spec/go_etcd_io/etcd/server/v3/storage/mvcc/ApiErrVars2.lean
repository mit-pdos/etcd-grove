/-
**DRAFT (mvccfull's Freeze list, item 3): `errVars2.law`, mvcc's four error variables, distinct.**
Candidate restatement of `mvcc.api.errVars.law` (`Api.lean`), side by side with it (the original
untouched). Scratch: not imported, not linked.

Two additions to `errVars.law`:

- **`ErrWatcherNotExist`** as `errors.New("mvcc: watcher does not exist")` (`watcher.go` l.30), the
  error `WatchStream.Cancel.contract` returns, which the tester's `Cancel` checks compare with.
- **The four variables hold distinct errors**: two of different messages (all four's are) are
  `errVarApart` (two `↦□` at the variables, of different values). `checkStoreRange` tests
  `err == ErrCompacted` where `err` may be `ErrFutureRev`'s value; `errorsNewVar` alone does not
  tell two variables apart (it gives each one's pointer and `Error()`'s result as a WP, from which
  no inequality of the pointers follows).

**Where it comes from.** mvcc's package fact `mvccInit` (`Proof/.../mvcc/Base.lean`, written by
`etc/gen-init.py`'s `SPECIAL['go_etcd_io.etcd.server.v3.storage.mvcc']`, proved in `Init.lean`) has
today, of these four: `errorsNewVar` of `ErrCompacted`, `ErrFutureRev`, `ErrEmptyWatcherRange`
(conjuncts 31-33: `errVars.law_holds`'s `H1 H2 H3`), the message cells (`errVarCell`) of
`ErrCompacted` and `ErrFutureRev` only (35-36, for the apply package's `ErrNoSpace` apartness), and of
`ErrWatcherNotExist` only `∃ e, ↦□ GoInterface.ok e` (conjunct 12). So `ErrCompacted`/`ErrFutureRev`'s
distinctness is derivable today (`errVarApart_of` on 35-36); `ErrEmptyWatcherRange`'s and
`ErrWatcherNotExist`'s is not, nor `ErrWatcherNotExist`'s `errorsNewVar`.

**The change to `mvccInit`** (a new 43rd conjunct at the end, `mvccInitErrExt` below; the 42 before
keep their positions): in gen-init.py's mvcc entry, the `'$inits'` lines for `WNE` and `EWR` use
`EtcdGrove.wp_New_errorString_cell as %x{t} ⟨#M{t}, #C{t}⟩` (as `CP`/`FR` do) in place of
`context.wp_New_errorString as %x{t} ⟨-, #M{t}⟩`; `finish` adds `ipersist HErrEmptyWatcherRange` and
the cells `#VEWR`, `#VWNE` (as `#VFR`) and `ErrWatcherNotExist`'s `errorsNewVar` (its `HErrWatcherNotExist`
and `MWNE`, framed by the final `unfold mvccInit EtcdGrove.errorsNewVar; iframe #`); and the new
conjunct goes after `reportVar reportCompactRevMu reportCompactRev` in the fact's text. Every
destructuring of `mvccInit` ends its pattern with `-` (which takes the new tail) but one:
`store__setupMetricsReporter.lean` l.32-33 names the last conjunct (`#G4⟩`) and becomes `#G4, -⟩`.
Then `errVars2.law_of_ext` below gives the law: `errVars2.law_holds` is that one-line glue.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **mvcc's error variables a client compares an error with** (`kvstore.go` l.38-39, `watcher.go`
l.30-31). -/
abbrev errVarNames : List GoString :=
  [ErrCompacted, ErrFutureRev, ErrEmptyWatcherRange, ErrWatcherNotExist]

/-- **mvcc's error variables are `errors.New`'s, and distinct** (DRAFT, item 3): the package's
initialization gives `ErrCompacted`, `ErrFutureRev`, `ErrEmptyWatcherRange` and `ErrWatcherNotExist`
as `*errors.errorString` values with their messages (`errorsNewVar`), so a client's `err == X` (Go's
interface `==`) is provable without mvcc's internals; and any two different variables of the four
hold different values (`errVarApart`), so `err == ErrCompacted` is false of `ErrFutureRev`'s value.
True of the code: each is its own `errors.New` call with its own literal message, and the four
messages differ (the proof's argument, not the client's: review round 1's F3.1 stated the apartness
over the variables, not their messages). -/
abbrev errVars2.law : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ⊢
    EtcdGrove.errorsNewVar ErrCompacted go!"mvcc: required revision has been compacted" ∗
    EtcdGrove.errorsNewVar ErrFutureRev go!"mvcc: required revision is a future revision" ∗
    EtcdGrove.errorsNewVar ErrEmptyWatcherRange go!"mvcc: watcher range is empty" ∗
    EtcdGrove.errorsNewVar ErrWatcherNotExist go!"mvcc: watcher does not exist" ∗
    □ (∀ (X Y : GoString), ⌜X ∈ errVarNames ∧ Y ∈ errVarNames ∧ X ≠ Y⌝ -∗
        EtcdGrove.errVarApart X Y)

/-- **Existing callers are unaffected**: `errVars.law` is its first three conjuncts (in the same
order, so a caller's `icases … with ⟨-, -, #HeEmp⟩` reads the same with a trailing `-`; or it keeps
`errVars.law`, now this corollary). -/
theorem errVars_of_errVars2 (h : errVars2.law (GF := GF)) : errVars.law (GF := GF) := by
  iintro #Hpkg
  ihave ⟨#H1, #H2, #H3, -⟩ := h $$ Hpkg
  iframe H1 H2 H3

/-- **A client's use**: `ErrCompacted` and `ErrFutureRev` hold different values (the names' membership
by position, their difference by `simp` on the two names). -/
theorem errVars2.compacted_ne_future (h : errVars2.law (GF := GF)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ⊢
      EtcdGrove.errVarApart ErrCompacted ErrFutureRev := by
  iintro #Hpkg
  ihave ⟨-, -, -, -, #Hap⟩ := h $$ Hpkg
  ispecialize Hap $$ %ErrCompacted %ErrFutureRev
  iapply Hap
  ipureintro
  exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self,
    by simp [ErrCompacted, ErrFutureRev]⟩

/-- **The proposed new last conjunct of `mvccInit`** (`etc/gen-init.py`'s mvcc entry): the message
cells of `ErrEmptyWatcherRange` and `ErrWatcherNotExist` (as `ErrCompacted`'s and `ErrFutureRev`'s,
conjuncts 35-36) and `ErrWatcherNotExist`'s `errorsNewVar`. One conjunct, parenthesized, so it is a
single positional element after `reportVar reportCompactRevMu reportCompactRev`. -/
abbrev mvccInitErrExt : IProp GF :=
  iprop(EtcdGrove.errorsNewVar ErrWatcherNotExist go!"mvcc: watcher does not exist" ∗
    EtcdGrove.errVarCell ErrEmptyWatcherRange go!"mvcc: watcher range is empty" ∗
    EtcdGrove.errVarCell ErrWatcherNotExist go!"mvcc: watcher does not exist")

/-- **The law from `mvccInit` with the new conjunct** (here a premise: `mvccInit` is not changed by
this draft; once it is, `hext` is `isPkgInit_access` and the pattern `⟨-, …(42)…, H⟩`). The four
cells (two from `mvccInit` today, two from the new conjunct) make the cells of the four variables
at their messages, and `errVarApart_of` gives two different variables apart (their messages differ). -/
theorem errVars2.law_of_ext
    (hext : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ⊢
      mvccInitErrExt (GF := GF)) :
    errVars2.law (GF := GF) := by
  iintro #Hpkg
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, #N1, #N2, #N3, -, #C1, #C2, -⟩
  ihave ⟨#N4, #C3, #C4⟩ := hext $$ Hpkg
  iframe N1 N2 N3 N4
  imodintro
  iintro %X %Y %hm
  obtain ⟨hX, hY, hne⟩ := hm
  -- the messages, the proof's: each variable's cell, and two different variables' messages differ
  let ms : List (GoString × GoString) :=
    [(ErrCompacted, go!"mvcc: required revision has been compacted"),
     (ErrFutureRev, go!"mvcc: required revision is a future revision"),
     (ErrEmptyWatcherRange, go!"mvcc: watcher range is empty"),
     (ErrWatcherNotExist, go!"mvcc: watcher does not exist")]
  have key : ∃ m m' : GoString, (X, m) ∈ ms ∧ (Y, m') ∈ ms ∧ m ≠ m' := by
    simp only [errVarNames, List.mem_cons, List.not_mem_nil, or_false] at hX hY
    rcases hX with rfl | rfl | rfl | rfl <;> rcases hY with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl hne
      | exact ⟨_, _,
          by first
            | exact List.mem_cons_self
            | exact List.mem_cons_of_mem _ List.mem_cons_self
            | exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
            | exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ List.mem_cons_self)),
          by first
            | exact List.mem_cons_self
            | exact List.mem_cons_of_mem _ List.mem_cons_self
            | exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
            | exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ List.mem_cons_self)),
          by decide⟩
  obtain ⟨m, m', hXm, hYm, hmm⟩ := key
  ihave #Hcells : (EtcdGrove.errVarCells ms : IProp GF) $$ []
  · unfold EtcdGrove.errVarCells EtcdGrove.errVarCells EtcdGrove.errVarCells EtcdGrove.errVarCells
      EtcdGrove.errVarCells
    iframe C1 C2 C3 C4
  ihave #HX := EtcdGrove.errVarCells_mem (GF := GF) hXm $$ Hcells
  ihave #HY := EtcdGrove.errVarCells_mem (GF := GF) hYm $$ Hcells
  iapply EtcdGrove.errVarApart_of X Y m m' hmm $$ HX HY

end laws

end api
end mvcc
end EtcdGrove
end Perennial
