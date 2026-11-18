/-
The watcher group (`watcher_group.go`): a set of watcher pointers, indexed by key (the
single-key watchers, `keyWatchers`) and by interval (the range watchers, in the interval tree
`ranges`, through its contract `adt.ownIvt`), with the set of all members (`watchers`).
Lean-first (no Rocq counterpart); see `notes/decisions.md`, "The watcher group and the stream
(unit 2)".

**Representation.** A watcher's range (`key`, `end`) and `startRev`, `id`, `fcs` are written
by `watch()` only, before the watcher is shared: a persistent fact of its pointer
(`watcherFixed w r fcs`, as a key index's `kiKey`). `ownWatcherGroup wg W` holds the group at
`wg` with the members `W` (pointer ↦ range): the all-watchers set holds `dom W`; the key map
has one non-empty set per key of a single-key member (`keyMembers W k`); the tree has one
entry per distinct interval of the range members, in the tree's order, its value the set
(`ivlMembers W ivl`) as an interface value of the named map type `watcherSet`. The members'
mutable fields (`minRev`, `victim`, `compacted`, `restore`, `ch`: `watcherOwn`) are not the
group's: the store's, or the batch's (unit 2a2).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-! ## Ranges and members (pure) -/

/-- A watcher's fixed range: a single key (`end == nil`, `end? = none`), or `[key, end)` under
the affine order (`end` empty, non-nil, is +∞: a `WithFromKey` watch); and its `startRev` and
`id`, fixed too. -/
structure WatchRange where
  key : GoString
  end? : Option GoString
  startRev : w64
  id : w64

/-- The key `k` is in the range. -/
def WatchRange.covers (r : WatchRange) (k : GoString) : Bool :=
  match r.end? with
  | none => decide (k = r.key)
  | some e => decide (adt.affCmp k r.key ≥ 0 ∧ adt.affCmp k e < 0)

/-- The members (of `W`) whose range satisfies `p`, as a set. -/
def membersBy (W : GMap Loc WatchRange) (p : WatchRange → Bool) : GMap Loc Unit :=
  GMap.fmap (fun _ => ()) (GMap.filter (fun _ r => p r) W)

/-- The single-key members of the key `k`. -/
def keyMembers (W : GMap Loc WatchRange) (k : GoString) : GMap Loc Unit :=
  membersBy W fun r => r.end? = none && decide (r.key = k)

/-- The range members of the interval `ivl`. -/
def ivlMembers (W : GMap Loc WatchRange) (ivl : adt.IvlS) : GMap Loc Unit :=
  membersBy W fun r => decide (r.end?.map (fun e => (r.key, e)) = some ivl)

/-! ## The point interval of a key -/

section pure
open adt

end pure

/-! ## The ranges holding a key -/

section ranges
variable [GooseExts]

end ranges

/-! ## The tree's entries under a change of members -/

section rangesOk
variable [GooseExts]

/-- The entries `L` of the interval tree of the members `W`: in the tree's order, one per
distinct interval of the range members, each with its set. -/
def RangesOk (W : GMap Loc WatchRange) (L : List adt.Entry) : Prop :=
  L.Pairwise (fun a b => adt.ivlLt a.1 b.1) ∧
  ∀ ivl, ivl ∈ L.map Prod.fst ↔ ∃ w r e, W !! w = some r ∧ r.end? = some e ∧ ivl = (r.key, e)

end rangesOk

/-! ## A loop's prefix of a set -/

/-! ## Ownership -/

section reprs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The watcher's fields that are never written after `watch()` builds it (persistent): `key`,
`end` (`nil` for a single key), `startRev`, `id`, `fcs`. -/
def watcherFixed (w : Loc) (r : WatchRange) (fcs : GoSlice) : IProp GF :=
  iprop(⌜w ≠ null⌝ ∗
    ∃ ks es : GoSlice, w.[watcher, go!"key"] ↦□ ks ∗ ks ↦*□ r.key ∗
      w.[watcher, go!"end"] ↦□ es ∗
      (match r.end? with
       | none => ⌜es = slice.nil⌝
       | some e => ⌜es ≠ slice.nil⌝ ∗ es ↦*□ e) ∗
      w.[watcher, go!"startRev"] ↦□ r.startRev ∗ w.[watcher, go!"id"] ↦□ r.id ∗
      w.[watcher, go!"fcs"] ↦□ fcs)

/-- The watcher's mutable fields (not the group's: the store's, or a batch's). -/
structure WatcherSt where
  minRev : w64
  victim : Bool
  compacted : Bool
  restore : Bool
  ch : GoChan

/-- The watcher's mutable fields hold `st` (at the fraction `q`: the watchable store's lock
invariant at its read side). -/
def watcherOwn (w : Loc) (st : WatcherSt) (q : Qp := 1) : IProp GF :=
  iprop(w.[watcher, go!"minRev"] ↦{DFrac.own q} st.minRev ∗
    w.[watcher, go!"victim"] ↦{DFrac.own q} st.victim ∗
    w.[watcher, go!"compacted"] ↦{DFrac.own q} st.compacted ∗
    w.[watcher, go!"restore"] ↦{DFrac.own q} st.restore ∗
    w.[watcher, go!"ch"] ↦{DFrac.own q} st.ch)

/-- The watcher set `m` (a `map[*watcher]struct{}`) holds exactly `S` (at the fraction `q`). -/
def ownWatcherSet (m : GoMap) (S : GMap Loc Unit) (q : Qp := 1) : IProp GF :=
  iprop(ownMap m (DFrac.own q) S)

/-- The key map `km` (`watcherSetByKey`) of the members `W`: one non-empty set per key of a
single-key member, holding the single-key members of that key. -/
def ownKeyMap (km : GoMap) (KM : GMap GoString GoMap) (W : GMap Loc WatchRange) (q : Qp := 1) :
    IProp GF :=
  iprop(ownMap km (DFrac.own q) KM ∗
    ⌜∀ k, (KM !! k).isSome ↔ ∃ w r, W !! w = some r ∧ r.end? = none ∧ r.key = k⌝ ∗
    [∗map] k ↦ m ∈ KM, ownWatcherSet m (keyMembers W k) q)

/-- An entry of the tree is a range set: its value is the set (as an interface value of the
named type `watcherSet`) of the range members of its interval. -/
def rangeSet (W : GMap Loc WatchRange) (z : adt.Entry) (q : Qp := 1) : IProp GF :=
  iprop(∃ m : GoMap, ⌜z.2 = interface.mkOk watcherSet.ty #m⌝ ∗ ownWatcherSet m (ivlMembers W z.1) q)

/-- The group at `wg` holds the members `W` (pointer ↦ range): the all-watchers set, the key
map, the interval tree, consistent with `W`, and the members' fixed fields; at the fraction `q`
(the watchable store's read lock: `ownWatcherGroup_split`, through the tree's pending
fractionality; the group's operations at `1`). -/
def ownWatcherGroup (wg : Loc) (W : GMap Loc WatchRange) (q : Qp := 1) : IProp GF :=
  iprop(∃ (km ws t : Loc) (KM : GMap GoString GoMap) (L : List adt.Entry),
    "Hwg" ∷ typedPointsto wg
      ({ keyWatchers' := km,
         ranges' := interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.adt.intervalTree.ty) #t,
         watchers' := ws } : watcherGroup) (DFrac.own q) ∗
    "Hws" ∷ ownWatcherSet ws (domSet W) q ∗
    "#Hfixed" ∷ ([∗map] w ↦ r ∈ W, ∃ fcs, watcherFixed w r fcs) ∗
    "Hkm" ∷ ownKeyMap km KM W q ∗
    "Hivt" ∷ adt.ownIvt t L q ∗
    "%HL" ∷ ⌜RangesOk W L⌝ ∗
    "Hranges" ∷ [∗list] z ∈ L, rangeSet W z q)

end reprs

end mvcc
end EtcdGrove
end Perennial
