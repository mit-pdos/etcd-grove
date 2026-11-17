/-
Lean-first (no Rocq counterpart).

# Kubernetes' checker's `Replay` and `WatchValidator`, as pure functions (k8s 7g step 2)

`examples/k8s/etcd3/correctness/replay.go` and `watch.go` (upstream's), on the driver's requests
and the store's responses and events, over the pure `Model` of `RModel.lean`:

- `RReplay`, `replayL`: `NewReplay(initialState, history)`: every operation `Step`s the state
  (`rstepL`), the history fails at the first step that does not; `states` maps each resource
  version to the last state at it (a later state at the same version replaces it, as Go's
  `states[state.ResourceVersion] = state`), `changes` lists the writes' changes in order;
- `rvalidateL` (`Replay.Validate`): `rreplayGetL` (a stale get matches the get on some state
  from its resource version on, with or without the prefix) and `rreplayListL` (a stale list is
  the list on the state at its response's resource version, up to `equalListResponse`);
- `REv`: a `watch.Event`, its type (the `EventType` string) and its object (the driver's `*Obj`, a
  `*metav1.Status` with its `Status` field, or anything else);
- `validateWatchL` (`ValidateWatch`, on a request `checkWatch` accepts, the driver's, and a
  response without error, as `realCheck` builds it): `lastErrOkL`, `bookmarksOkR`, for a
  watch-list `splitInitL` and `initialOkL`, and `reliableOkR` (`watchRangeL`, `eventsForRVsL`,
  `toWatchEventL`); events are compared by `compareEventsL` (`toEventReference`'s references, by
  `cmp.Diff`, then the objects, by `reflect.DeepEqual`);
- `realOkL`: the replay and every check after porcupine's run (`realCheck`'s second half).

The watch request is `WatchRequest{Key: in.WKey, Options: watchOptions(in)}` (`watch.go` of the
driver): resource version `MinRV`, match `matchOpt(in)`, the predicate `predicate(in)` (with
`AllowWatchBookmarks`), recursive `Recursive`, `SendInitialEvents` true iff `SendInit = 2`.
`objectRV` reads an object's resource version through `meta.Accessor` and the versioner: the
field of a `*Obj` (`parseRVD_rvStr`), an error for anything else; `keyFunc` (the driver's) is the
store key of a `*Obj`'s namespace and name; `HasInitialEventsEndBookmarkAnnotation` is a `*Obj`'s
`Annotated`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.RModel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open k8s_etcd3 k8sDeep
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input)

section go
variable [GooseExts]

/-! ## The replay (`replay.go`) -/

/-- **A `*Replay`'s contents**: the states by resource version and the changes in order (its
`newFunc` and `versioner` are the driver's). -/
structure RReplay where
  states : GMap w64 RM
  changes : List RChange

/-- One iteration of `NewReplay`'s loop on `(state, states, changes)`: the operation must `Step`. -/
def replayStepL (acc : Option (RM × GMap w64 RM × List RChange)) (op : Input × RResp) :
    Option (RM × GMap w64 RM × List RChange) :=
  match acc with
  | none => none
  | some (st, ss, cs) =>
    if (rstepL op.1 st op.2).1 then
      some ((rstepL op.1 st op.2).2.1,
        <[(rstepL op.1 st op.2).2.1.rv := (rstepL op.1 st op.2).2.1]> ss,
        cs ++ (rstepL op.1 st op.2).2.2.toList)
    else none

/-- **`NewReplay(initialState, history)`**: from the initial state (a clone, of equal contents)
at its resource version, every operation in order; none (an error) if one does not `Step`. -/
def replayL (init : RM) (ops : List (Input × RResp)) : Option RReplay :=
  (ops.foldl replayStepL (some (init, {[init.rv := init]}, []))).map fun r => ⟨r.2.1, r.2.2⟩

/-- **`Replay.validateGet(req, resp)`**: a consistent get (no `MinRV`), a `MinRV` that does not
parse and a too-large response pass; otherwise the response must be some state's `get`, from
the requested resource version on, with its prefix or without (the cacher's "not found"). The
range over `states` is Go's map range: the answer is an `any`, whatever the order. -/
def rreplayGetL (R : RReplay) (x : Input) (resp : RResp) : Bool :=
  if x.MinRV' = [] then true
  else match parseRVD x.MinRV' with
    | none => true
    | some reqRV =>
      isTooLargeE resp.err ||
        R.states.toList.any fun rs => decide (uint.nat reqRV ≤ uint.nat rs.1) &&
          (respEqL (rgetL x rs.2) resp || respEqL (rgetL x { rs.2 with pfx := [] }) resp)

/-- **`Replay.validateList(req, resp)`**: an error response, and a consistent list, pass; an
error of `ListReadConsistency` fails; otherwise the response must be a list (a nil object or
another type fails) whose resource version has a state, and `equalListResponse` there with the
list on that state. -/
def rreplayListL (R : RReplay) (x : Input) (resp : RResp) : Bool :=
  if errNonNil resp.err then true
  else match listConsL x with
    | none => false
    | some (.consistent, _) => true
    | some _ =>
      match resp.obj with
      | .list _ rv _ _ =>
        match R.states !! rv with
        | some st => equalListRespL x st (rlistL x st) resp
        | none => false
      | _ => false

/-- **`Replay.Validate(realRequest(in), resp)`**: gets and lists; writes pass. -/
def rvalidateL (R : RReplay) (x : Input) (resp : RResp) : Bool :=
  if x.Kind' = W64 4 then rreplayListL R x resp
  else if x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2 then true
  else rreplayGetL R x resp

/-! ## Watch events -/

/-- A watch event's object: the driver's `*Obj`, a `*metav1.Status` (its `Status` field), or any
other dynamic type. -/
inductive REvObj where
  | obj (o : Obj)
  | status (s : GoString)
  | other
deriving DecidableEq

/-- **A `watch.Event`**: its type and its object. -/
structure REv where
  ty : GoString
  o : REvObj
deriving DecidableEq

/-- The event types (`watch.Added`, ...). -/
def evAdded : GoString := go!"ADDED"
def evModified : GoString := go!"MODIFIED"
def evDeleted : GoString := go!"DELETED"
def evBookmark : GoString := go!"BOOKMARK"
def evError : GoString := go!"ERROR"

/-- `objectRV(obj, versioner)`: a `*Obj`'s resource version; an error for anything else. -/
def objRVL : REvObj → Option w64
  | .obj o => some o.ResourceVersion'
  | _ => none

/-- `storage.HasInitialEventsEndBookmarkAnnotation(obj)`: a `*Obj`'s annotation bit. -/
def annotL : REvObj → Option Bool
  | .obj o => some o.Annotated'
  | _ => none

/-- The driver's `keyFunc(obj)`: a `*Obj`'s store key. -/
def keyOfL : REvObj → Option GoString
  | .obj o => some (storeKeyL (o.Namespace' ++ go!"/" ++ o.Name'))
  | _ => none

/-- `filterOutBookmarksAndErrors(events)`. -/
def filterBE (evs : List REv) : List REv :=
  evs.filter fun e => !(decide (e.ty = evBookmark) || decide (e.ty = evError))

/-! ## The checks (`watch.go`) -/

/-- **`validateMaybeLastEventError(events)`**: every Error event holds a `*metav1.Status` of
status `Failure` and is the last event. -/
def lastErrOkL (evs : List REv) : Bool :=
  evs.zipIdx.all fun ei =>
    if ei.1.ty = evError then
      match ei.1.o with
      | .status s => decide (s = go!"Failure") && decide (ei.2 + 1 = evs.length)
      | _ => false
    else true

/-- One iteration of `validateBookmarks`' loop on (the last bookmark's revision, the last event's,
whether an initial-events-end bookmark was seen); none: an error. Errors are skipped. -/
def bmStepR : Option (w64 × w64 × Bool) → REv → Option (w64 × w64 × Bool)
  | none, _ => none
  | some (lb, le, f), e =>
    if e.ty = evError then some (lb, le, f)
    else match objRVL e.o with
      | none => none
      | some rv =>
        if e.ty = evBookmark then
          if uint.nat rv < uint.nat lb ∨ uint.nat rv < uint.nat le then none
          else match annotL e.o with
            | none => none
            | some a => if a then (if f then none else some (rv, le, true)) else some (rv, le, f)
        else if uint.nat rv ≤ uint.nat lb then none
        else some (lb, wmax le rv, f)

/-- **`validateBookmarks(events)`**: bookmarks do not go back, below the last bookmark or the last
event; events come after the last bookmark; at most one initial-events-end bookmark. -/
def bookmarksOkR (evs : List REv) : Bool := (evs.foldl bmStepR (some (0, 0, false))).isSome

/-- **`splitInitialEvents(events)`**: at the first bookmark, which must be annotated, the events
before it and the rest (from it); with no bookmark, nothing (`([], [])`, the watch ended before
the bookmark) if only bookmarks and errors, else an error (none). -/
def splitInitL (evs : List REv) : Option (List REv × List REv) :=
  match evs.findIdx? (fun e => decide (e.ty = evBookmark)) with
  | some i =>
    match annotL (evs.getD i ⟨[], .other⟩).o with
    | some true => some (evs.take i, evs.drop i)
    | _ => none
  | none => if (filterBE evs).isEmpty then some ([], []) else none

/-- `toEventReference`'s reference of an event: its key, type and resource version. -/
def evRefL (e : REv) : Option (GoString × GoString × w64) :=
  match keyOfL e.o, objRVL e.o with
  | some k, some rv => some (k, e.ty, rv)
  | _, _ => none

/-- **`compareEvents(expected, got)`**: both have references (`toEventReference`, a non-nil
slice), equal ones (`cmp.Diff` is `""`), and equal objects (`reflect.DeepEqual`, event by
event). -/
def compareEventsL (exp got : List REv) : Bool :=
  match exp.mapM evRefL, got.mapM evRefL with
  | some er, some gr => decide (er = gr) && decide (exp.map REv.o = got.map REv.o)
  | _, _ => false

/-- **`Replay.InitialEvents(request, rv)`**: an Added event for each item the watch selects in the
state at `rv` (`initialEvents`, `listItems`), in key order; none if no state is at `rv`. -/
def initialEventsR (R : RReplay) (x : Input) (rv : w64) : Option (List REv) :=
  (R.states !! rv).map fun st => (listItemsL x x.WKey' st).map fun o => ⟨evAdded, .obj o⟩

/-- **`validateInitialEvents(request, initialEvents, bookmarkRV)`**: the bookmark not older than a
requested resource version (other than `""` and `"0"`), and the initial events those of the state
at the bookmark's resource version. -/
def initialOkL (R : RReplay) (x : Input) (init : List REv) (brv : w64) : Bool :=
  (if x.MinRV' ≠ [] ∧ x.MinRV' ≠ go!"0" then
    match parseRVD x.MinRV' with
    | none => false
    | some req => decide (uint.nat req ≤ uint.nat brv)
  else true) &&
  match initialEventsR R x brv with
  | none => false
  | some exp => compareEventsL exp init

/-- `math.MaxUint64`. -/
def maxU64 : w64 := W64 (2 ^ 64 - 1)

/-- One iteration of `eventResourceVersionRange`'s loop on `(minRV, maxRV)`; none: an error (an
object without a resource version, an unknown type). Errors are skipped. -/
def evRangeStepR (acc : Option (w64 × w64)) (e : REv) : Option (w64 × w64) :=
  match acc with
  | none => none
  | some (mn, mx) =>
    if e.ty = evError then some (mn, mx)
    else match objRVL e.o with
      | none => none
      | some rv =>
        if e.ty = evAdded ∨ e.ty = evDeleted ∨ e.ty = evModified then
          some (wmin mn rv, wmax mx (rv + W64 1))
        else if e.ty = evBookmark then some (wmin mn (rv + W64 1), wmax mx rv)
        else none

/-- **`eventResourceVersionRange(events)`**: none for an error; `some none` for no range (no event
or bookmark marks one); else `[Min, Max)`. -/
def evRangeR (evs : List REv) : Option (Option (w64 × w64)) :=
  match evs.foldl evRangeStepR (some (maxU64, 0)) with
  | none => none
  | some (mn, mx) => if mn = maxU64 ∨ mx = 0 then some none else some (some (mn, mx))

/-- **`watchRevisionRange(versioner, request, events)`**: the events' range, its start raised by
the request: past the requested resource version for `NotOlderThan` (if positive), at it plus
one for `Exact` (an error at `0`) and for the legacy match (if positive). -/
def watchRangeL (x : Input) (evs : List REv) : Option (Option (w64 × w64)) :=
  match evRangeR evs with
  | none => none
  | some none => some none
  | some (some (mn, mx)) =>
    match parseRVD x.MinRV' with
    | none => none
    | some req =>
      if x.Match' = W64 1 then
        some (some (if 0 < uint.nat req then wmax mn (req + W64 1) else mn, mx))
      else if x.Match' = W64 2 then (if req = 0 then none else some (some (req + W64 1, mx)))
      else some (some (if 0 < uint.nat req then req + W64 1 else mn, mx))

/-- **`Change.toWatchEvent(versioner, predicate(in))`**: Modified if the predicate matches the
object and the one before, Added if only the object, Deleted (the one before at the change's
resource version, `UpdateObject`) if only the one before, none otherwise. -/
def toWatchEventL (x : Input) (c : RChange) : Option REv :=
  let cm := c.obj.any (selOkL x)
  let pm := c.prev.any (selOkL x)
  if cm && pm then c.obj.map fun o => ⟨evModified, .obj o⟩
  else if cm then c.obj.map fun o => ⟨evAdded, .obj o⟩
  else if pm then c.prev.map fun o => ⟨evDeleted, .obj { o with ResourceVersion' := c.rv }⟩
  else none

/-- **`Replay.EventsForRVs(request, &ResourceVersionRange{mn, mx})`**: the events of the changes at
resource versions in `[mn, mx)` whose key the watch has in scope, in order. -/
def eventsForRVsL (R : RReplay) (x : Input) (mn mx : w64) : List REv :=
  R.changes.filterMap fun c =>
    if uint.nat mn ≤ uint.nat c.rv ∧ uint.nat c.rv < uint.nat mx ∧
        keyInScopeL x.WKey' x.Recursive' c.key = true then toWatchEventL x c
    else none

/-- **`validateReliable(request, events)`**: no range passes; else the events (bookmarks and errors
aside) are the changes' events over the range. -/
def reliableOkR (R : RReplay) (x : Input) (evs : List REv) : Bool :=
  match watchRangeL x evs with
  | none => false
  | some none => true
  | some (some (mn, mx)) => compareEventsL (eventsForRVsL R x mn mx) (filterBE evs)

/-- **`ValidateWatch(request, WatchResponse{Events: evs})`** on a request `checkWatch` accepts:
the errors, the bookmarks, for a watch-list (`SendInit = 2`) the split at the initial-events-end
bookmark (nothing more to check if the events end before it) and the initial events at its
resource version, then the events from it (or all of them) over the revisions they mark. -/
def validateWatchL (R : RReplay) (x : Input) (evs : List REv) : Bool :=
  lastErrOkL evs && bookmarksOkR evs &&
    if x.SendInit' = W64 2 then
      match splitInitL evs with
      | none => false
      | some (_, []) => true
      | some (init, b :: rest) =>
        match objRVL b.o with
        | none => false
        | some brv => initialOkL R x init brv && reliableOkR R x (b :: rest)
    else reliableOkR R x evs

/-! ## The verdict after porcupine -/

/-- **`realCheck`'s checks after porcupine's run**, on the linearized unary operations `ops` and
the watches `ws` (each its input and its events as given to the validator): `NewReplay` from the
initial model, `Validate` of every operation, `ValidateWatch` of every watch. -/
def realOkL (init : RM) (ops : List (Input × RResp)) (ws : List (Input × List REv)) : Bool :=
  match replayL init ops with
  | none => false
  | some R => ops.all (fun op => rvalidateL R op.1 op.2) && ws.all (fun w => validateWatchL R w.1 w.2)

/-! ## Facts -/

theorem replayStepL_none (ops : List (Input × RResp)) :
    ops.foldl replayStepL none = none := by
  induction ops with
  | nil => rfl
  | cons _ _ ih => simpa [List.foldl, replayStepL] using ih

/-- `NewReplay` on a history with one more operation: the replay so far, then its step. -/
theorem replayL_snoc (init : RM) (ops : List (Input × RResp)) (op : Input × RResp) :
    (ops ++ [op]).foldl replayStepL (some (init, {[init.rv := init]}, [])) =
      replayStepL (ops.foldl replayStepL (some (init, {[init.rv := init]}, []))) op := by
  rw [List.foldl_append]; rfl

end go

end k8s_correctness
end EtcdGrove
end Perennial
