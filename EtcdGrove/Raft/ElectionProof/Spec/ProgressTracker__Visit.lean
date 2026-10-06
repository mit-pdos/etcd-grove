/-
Port of `election_proof/spec_ProgressTracker__Visit.v`.
-/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **This statement was FALSE until 2026-09-16** and is now repaired. The repair is
recorded here rather than silently applied, because a `Qed` resting on a false
`Admitted` is unsound and `proof_raft__reset.v` -- hence `becomeFollower`,
`becomeCandidate`, `becomeLeader` and everything above them -- was resting on this one.

**What was wrong.** The precondition owned no part of the tracker *struct*.
`ownTracker cfg tv votes` is indexed by the tracker *value* and owns what that value
points at -- the vote map, the progress map, the id sets -- not the bytes of `trk`
itself. But `Visit` has a pointer receiver and its very first statement is
`n := len(p.Progress)`, which Goose translates to

    ![tracker.ProgressMap]
      (StructFieldRef ProgressTracker "Progress"
         (![go.PointerType ProgressTracker] "p"))

-- a load through `trk.[tracker.ProgressTracker, go!"Progress"]` (Rocq
new/code/go_etcd_io/raft/v3/tracker.v:809). It reads that field again inside the
second range, for the `map.lookup1` that produces each `pr` (tracker.v:837). So the
triple asserted safety of a load from a location it did not own. Measured with two
probes, each `rocq compile -vok` RC=0:

  - precondition as it was: `wp_start; iNamed "Hown"; wp_auto` parks immediately, with
    the whole body still to run;
  - precondition plus `trk ↦ tv`: the same three tactics get through the receiver
    alloc, the field load and the `len` call's argument.

The comment that used to sit here claimed "`Visit` reads the progress map out of the
tracker value it is given and does not mutate the tracker itself, so it does not need
the location". The second half is true and the first is not -- it reads the map
*reference* out of the struct, through the pointer. Mutation was never the question;
any read through the receiver is. An invariant promised in prose and absent from the
conjuncts, which is the same failure as the `r.step` one; see main's notes/STATUS.md's
table.

**The repair**, applied: `trk ↦ tv` in the pre- and postcondition, and lent to the
closure as well (`visitClosure cfg trk votes prs f I`, `InvTracker.lean`). Lending is
necessary, not cosmetic -- see that definition's comment. `proof_raft__reset.v` keeps
the field split out with its `raft_split_trk` instead of re-assembling it after
`ResetVotes`, and its closure applies the continuation wand to read
`r.trk.MaxInflight` and re-splits before returning.

**The statement is now true, and proved** (2026-09-20, `proof_ProgressTracker__Visit.v`).
Two tooling obstacles had to be fixed first (2026-09-17); both were unrelated to raft:

1. `var sl [7]uint64; if len(sl) >= n` asks for `len` of an *array*. There was **no**
   `FuncUnfold go.len [go.ArrayType n t]` instance anywhere under Rocq `new/golang/`
   (`go.len_underlying` does not help: an array type is already its own underlying
   type), *and* Goose emitted `FuncResolve go.len [go.ArrayType 7 go.uint64] #()` with
   no operand applied -- a function value used as an integer. Goose now folds the
   constant, so the code reads `#(W64 7) >=⟨go.int⟩ ![go.int] "n"` (tracker.v:814), and
   `go.len_array` / `pure_wp_array_len` cover the non-constant case. (Contrast maps,
   where the instance exists but only at the literal `go.MapType`;
   `wp_ProgressMap_len` in `InvTracker.lean` is that workaround.)
2. `ids = sl[:n]` was translated as `Slice` applied to the array *value*, where
   `slice_array_step` (Rocq new/golang/defn/array.v) steps only on an array
   *location*. Goose now passes the address:
   `let: "$s" := "sl" in Slice (go.ArrayType 7 go.uint64) ("$s", #(W64 0), ![go.int] "n")`
   (tracker.v:816-817). This was also a *semantic* fix independent of the model -- in
   Go `sl[:n]` aliases `sl`, and a slice of a copy does not.

The `else` branch (`make([]uint64, n)`, taken when `size cfg > 7`) was always fine.

**The proof** (`proof_ProgressTracker__Visit.v`, lemma `wp_visit`) runs the body in
three phases. The `if` is joined with `wp_if_join` at "`ids` points at a slice of `n`
slots": the fast path turns the stack array's `sl ↦ (a : array w64 7)` into a slice
with `slice_array` and keeps the `n`-element prefix with `own_slice_split_all`; the
slow path is `wp_slice_make2`. Then a map range fills `ids` backwards from `n-1` --
with `wp_map_for_range`, which hands the map's ownership back (the map is needed again
afterwards) -- so that `ids` ends as `reverse keys`. `wp_slices_Sort`
(`spec_slices_Sort.v`) permutes it, and a `slice.for_range` applies `visitClosure` to
each id, taking that id's `ownProgress` out of `Hprogs` with `big_sepM_lookup_acc`.
Every element of the sorted slice is a key of `prs`, which is what makes the
`p.Progress[id]` lookup hit. The sorted order is not observable -- no caller's `I`
mentions it -- so the permutation-only postcondition of `wp_slices_Sort` is enough.

**2026-09-20**, for `bcastAppend`, three changes to `visitClosure` (all explained where
it is defined, `InvTracker.lean`):

- the closure is lent the accessor wand back to the *whole* tracker and hands the whole
  tracker back, rather than being lent one `ownProgress` and handing that back.
  `bcastAppend`'s closure re-enters the tracker through `maybeSendAppend`'s own
  `r.trk.Progress[to]` lookup, so one `Progress` is not enough;
- it is told `i ∈ cfg`, which is what makes that lookup hit;
- the tracker *value* may change across the call, so this postcondition is existential
  in it. `ownRaftPhys` hides the struct value, so a closure that calls back into the
  raft struct cannot promise to return the field at the value it was handed.

The loop invariant here therefore carries `trk ↦ tv'` and `ownTracker cfg tv' votes`
at a value that moves, and re-splits one `Progress` out each iteration with
`ownTracker_lookup` -- which is possible only because the progress map is now held
read-only, so the key/pointer fact survives the rebuild. -/
abbrev tracker.ProgressTracker.Visit.spec : Prop :=
  ∀ (cfg : GSet w64) (trk : Loc) (tv : tracker.ProgressTracker) (votes : GMap w64 Bool)
    (prs : GMap w64 Loc) (pvs : GMap w64 (tracker.Progress × tracker.Inflights))
    (f : GoFunc) (I : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦ tv ∗
      ownTracker cfg tv votes prs pvs ∗ I ∗
      □ visitClosure cfg trk votes prs f I }}
    (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty @!! go!"Visit"))
      (Val #f))
  {{ RET #(); ∃ tv' pvs', trk ↦ tv' ∗ ownTracker cfg tv' votes prs pvs' ∗ I }}

end spec

end EtcdGrove
end Perennial
