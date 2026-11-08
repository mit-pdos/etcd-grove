/-
Lean-first (no Rocq counterpart).

# The driver's model: the watch check (stage 7f-2 of `notes/k8s-7f-scope.md`)

The driver's check of a watch (the Go `watchOk` of `examples/k8s/etcd3/watch.go`, a copy of
Kubernetes' `correctness.WatchValidator` against a configuration's history, with the departures
of the 7f Scope's §4.2), as pure functions:

- `WEv`, a watch event as the driver records it (its type `t`: 0 Added, 1 Modified, 2 Deleted,
  3 Bookmark, 4 Error, 5 bad; and its object), and the plain value an output carries,
  `encWEventsL` (`encodeWEvents`), with its decoding `decWEventsL` (`decodeWEvents`);
- `changeAtL` (`changeAt`: the first key whose item differs between two stores), `toEventL`
  (`toEvent`: a change's event for a watch's predicate), `initialEventsL` (`initialEvents`);
- `bookmarksOkL`, `reliableOkL`, `initialPrefixOkL` and **`watchOkL x y h`**, the check of the
  watch `x` with output `y` against the model's state `h` (a store and its history).

Revisions are natural numbers here (the store's `uint.nat`); the Go functions' 64-bit arithmetic
agrees below the bound on the store's revision (7f-6).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KList

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input Output item)

section go
variable [GooseExts]

/-! ## Watch events and their encoding -/

/-- A watch event as the driver records it (`WEvent`): its type (`WAdded` 0, `WModified` 1,
`WDeleted` 2, `WBookmark` 3, `WError` 4, `WBad` 5) and its object. -/
structure WEv where
  t : Nat
  o : Obj

/-- One event of `encodeWEvents`: its type and annotation bytes, its object's resource version,
its object's encoding's length, and that encoding. -/
def encWEvL (e : WEv) : GoString :=
  [W8 (e.t : Int), if e.o.Annotated' then W8 1 else W8 0] ++ rvBytes e.o.ResourceVersion' ++
    rvBytes (W64 ((encodeWith tagV1 e.o).length : Int)) ++ encodeWith tagV1 e.o

/-- `encodeWEvents(evs)`: the events' encodings, in order. -/
def encWEventsL (evs : List WEv) : GoString := (evs.map encWEvL).flatten

/-- An object with the resource version `rv` and the annotation `a`. -/
def withRvAnn (o : Obj) (rv : w64) (a : Bool) : Obj :=
  { o with ResourceVersion' := rv, Annotated' := a }

/-- `decodeWEvents(s)`: the events `s` encodes, or none. -/
def decWEventsL (s : GoString) : Option (List WEv) :=
  if h : s = [] then some []
  else if s.length < 18 then none
  else
    let r := s.drop 18
    let n := (bytesBE ((s.drop 10).take 8)).toNat
    if r.length < n then none
    else match decodeD (r.take n) with
      | none => none
      | some o =>
        (decWEventsL (r.drop n)).map fun rest =>
          WEv.mk ((s.headD (W8 0)).toNat)
            (withRvAnn o (bytesBE ((s.drop 2).take 8)) (decide ((s.drop 1).headD (W8 0) = W8 1)))
            :: rest
termination_by s.length
decreasing_by
  simp only [List.length_drop]
  have : s.length ≠ 0 := by simpa using h
  omega

/-! ## Changes and events -/

/-- A change: the write at revision `rv` of the key `key`, its item's object before and after
(none: absent). -/
structure Chg where
  key : GoString
  prev : Option Obj
  cur : Option Obj
  rv : Nat

/-- `changeAt(prev, cur, r)`: the first key, in key order, whose item differs between the
key-sorted item lists `p` and `c` (a merge of the two), or none. -/
def changeAtL : List item → List item → Nat → Option Chg
  | [], [], _ => none
  | p :: _, [], r => some ⟨p.key', some p.obj', none, r⟩
  | [], q :: _, r => some ⟨q.key', none, some q.obj', r⟩
  | p :: ps, q :: qs, r =>
    if decide (go.GoStringLt p.key' q.key') then some ⟨p.key', some p.obj', none, r⟩
    else if decide (go.GoStringLt q.key' p.key') then some ⟨q.key', none, some q.obj', r⟩
    else if decide (p = q) then changeAtL ps qs r
    else some ⟨p.key', some p.obj', some q.obj', r⟩

/-- `toEvent(in, ch)`: Modified if the watch's predicate matches the new and the old object,
Added if only the new, Deleted (the old object at the change's revision) if only the old. -/
def toEventL (x : Input) (ch : Chg) : Option WEv :=
  let cm := ch.cur.any (selOkL x)
  let pm := ch.prev.any (selOkL x)
  if cm && pm then (ch.cur.map fun o => ⟨1, o⟩)
  else if cm then (ch.cur.map fun o => ⟨0, o⟩)
  else if pm then (ch.prev.map fun o => ⟨2, { o with ResourceVersion' := W64 (ch.rv : Int) }⟩)
  else none

/-- `initialEvents(in, st)`: an Added event for each item in the watch's scope its predicate
matches, in key order. -/
def initialEventsL (x : Input) (st : GSt) : List WEv :=
  (st.items.filter fun it =>
    keyInScopeL x.WKey' x.Recursive' (storeKeyL it.key') && selOkL x it.obj').map
    fun it => ⟨0, it.obj'⟩

/-- The store at revision `r` of a history (`histAt`, with a natural index). -/
def histN (hs : List GSt) (r : Nat) : GSt := ((hs.take r).getLast?).getD zSt

/-- The event of a watch of `x` for the change at revision `r` of the history `hs`, if any (the
change's key in scope and its event for the predicate). -/
def evAtL (x : Input) (hs : List GSt) (r : Nat) : Option WEv :=
  if 2 ≤ r then
    (changeAtL (histN hs (r - 1)).items (histN hs r).items r).bind fun ch =>
      if keyInScopeL x.WKey' x.Recursive' (storeKeyL ch.key) then toEventL x ch else none
  else none

/-! ## The check -/

/-- `eventsEqual`: the same types and objects. -/
def evsEqL (a b : List WEv) : Bool := decide (a.map (fun e => (e.t, e.o)) = b.map (fun e => (e.t, e.o)))

/-- `validateBookmarks`'s loop state: the last bookmark's and the last event's revisions, and
whether an initial-events-end bookmark was seen. -/
def bmStepL : Option (Nat × Nat × Bool) → WEv → Option (Nat × Nat × Bool)
  | none, _ => none
  | some (lb, le, ann), e =>
    let rv := uint.nat e.o.ResourceVersion'
    if e.t = 3 then
      if rv < lb ∨ rv < le then none
      else if e.o.Annotated' then (if ann then none else some (rv, le, true))
      else some (rv, le, ann)
    else if rv ≤ lb then none
    else some (lb, max le rv, ann)

/-- `bookmarksOk(evs)`: `validateBookmarks` on the events that are not errors. -/
def bookmarksOkL (evs : List WEv) : Bool := (evs.foldl bmStepL (some (0, 0, false))).isSome

/-- The events' revision range (`eventResourceVersionRange`): an event at `r` covers `[r, r+1)`,
a bookmark at `b` covers `[b+1, b)`; none if no event or bookmark. -/
def evRangeL (evs : List WEv) : Option (Nat × Nat) :=
  evs.foldl (fun acc e =>
    let rv := uint.nat e.o.ResourceVersion'
    let (lo, hi) := if e.t = 3 then (rv + 1, rv) else (rv, rv + 1)
    match acc with
    | none => some (lo, hi)
    | some (lo', hi') => some (min lo lo', max hi hi')) none

/-- The events of the changes at revisions `[lo, hi)` (from 2: revision 1 is the empty store). -/
def eventsInL (x : Input) (hs : List GSt) (lo hi : Nat) : List WEv :=
  ((List.range' lo (hi - lo)).filterMap fun r => evAtL x hs r)

/-- `reliableOk(in, req, evs, c)`: the revisions the events mark, clipped by the request
(`watchRevisionRange`), at most the configuration's, and the events there exactly the changes'
events in scope (the bookmarks aside). -/
def reliableOkL (x : Input) (req : Nat) (evs : List WEv) (h : HSt) : Bool :=
  match evRangeL evs with
  | none => true
  | some (lo0, hi) =>
    let lo := if x.Match' = W64 1 then (if 0 < req then max lo0 (req + 1) else lo0)
      else if 0 < req then req + 1 else lo0
    if x.Match' = W64 2 ∧ req = 0 then false
    else if uint.nat h.st.rv + 1 < hi then false
    else evsEqL (eventsInL x h.hist lo hi) (evs.filter fun e => e.t ≠ 3)

/-- `initialPrefixOk(in, req, evs, c)`: the events are a prefix of the initial events at some
revision from the requested one (1 for none) to the configuration's. -/
def initialPrefixOkL (x : Input) (req : Nat) (evs : List WEv) (h : HSt) : Bool :=
  evs.isEmpty ||
    (List.range' (max req 1) (uint.nat h.st.rv + 1 - max req 1)).any fun r =>
      evsEqL ((initialEventsL x (histN h.hist r)).take evs.length) evs &&
        decide (evs.length ≤ (initialEventsL x (histN h.hist r)).length)

/-- **`watchOk(in, out, c)`**: a failed or skipped watch constrains nothing; an output that does
not decode, or with a bad event, is rejected; Error events are dropped wherever they are; every
other event's revision is at most the configuration's; then the bookmarks, the initial events at
the initial-events-end bookmark's revision for a watch-list (a prefix of them at some revision if
it ended before the bookmark), and the events over the revisions they mark. -/
def watchOkL (x : Input) (y : Output) (h : HSt) : Bool :=
  if y.WFailed' || x.Skip' then true
  else match decWEventsL y.WEvents' with
    | none => false
    | some all =>
      if all.any (fun e => 5 ≤ e.t) then false
      else
        let evs := all.filter fun e => e.t ≠ 4
        if evs.any (fun e => uint.nat h.st.rv < uint.nat e.o.ResourceVersion') then false
        else if !bookmarksOkL evs then false
        else match parseRVD x.MinRV' with
          | none => false
          | some reqw =>
            let req := uint.nat reqw
            if x.SendInit' = W64 2 then
              match evs.findIdx? (fun e => e.t = 3) with
              | none => initialPrefixOkL x req evs h
              | some b =>
                let bm := evs.getD b ⟨0, ⟨[], [], [], [], [], [], 0, false⟩⟩
                let brv := uint.nat bm.o.ResourceVersion'
                if !bm.o.Annotated' then false
                else if (req ≠ 0 ∧ brv < req) ∨ brv < 1 ∨ uint.nat h.st.rv < brv then false
                else if !evsEqL (initialEventsL x (histN h.hist brv)) (evs.take b) then false
                else reliableOkL x req (evs.drop b) h
            else reliableOkL x req evs h

end go

end k8s_etcd3
end EtcdGrove
end Perennial
