/-
**What authkv's checks compute** (the auth plan's E2f, 2026-10-25; `notes/decisions.md`, "E2f of
the auth plan"). Lean-first (no Rocq counterpart).

The pure functions the specs of `keyOf`, `Writer`, `SetupWrite`, `CheckHistory` and `LastIn`
(`examples/authkv/authkv.go`) return or check, over the events `common.Collect` gives (`wev`):
`keyOfK` the key `x/<who>/<n>`, `writerK` the principal a key names (the first of `principals`
with `x/<who>/` a proper prefix, for `x` in `a`, `c`), `setupWriteK` a repeat of a set-up put (a
put of a key of `setupKeys` with the value `setup`), `histOk` the history's check (every event
above the set-up's revision but the last write's and a repeated set-up put is one its key's
principal was permitted), `lastIn` the last revision in `[lo, hi)`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.Model
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.WatchBase

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open common

section checks
variable [GooseExts]

/-- The principals (`Principals()`), in order. -/
def principals : List GoString := [go!"u", go!"v", go!"anon", go!"bad"]

/-- The key prefixes' first parts (`Writer`'s inner loop), in order. -/
def keyParts : List GoString := [go!"a", go!"c"]

/-- The key `x/<who>/<n>` (`keyOf`). -/
def keyOfK (x who n : GoString) : GoString := x ++ go!"/" ++ who ++ go!"/" ++ n

/-- The prefix `x/<who>/` `Writer` compares a key with. -/
def keyPfx (x who : GoString) : GoString := x ++ go!"/" ++ who ++ go!"/"

/-- `p` is a proper prefix of `k` (`len(k) > len(p) && k[:len(p)] == p`). -/
def properPfx (k p : GoString) : Bool :=
  decide (p.length < k.length) && decide (k.take p.length = p)

/-- Some prefix `x/<who>/` of `who` is a proper prefix of `k`. -/
def namesWho (k who : GoString) : Bool := keyParts.any fun x => properPfx k (keyPfx x who)

/-- **The principal key `k` names** (`Writer(k)`): the first principal `who` with `x/<who>/` a
proper prefix of `k`, `""` if none. -/
def writerK (k : GoString) : GoString := (principals.find? (namesWho k)).getD []

/-- The keys `SetUp` puts, in order: `x/<who>/d` for every principal and `x` in `a`, `c`. -/
def setupKeys : List GoString :=
  principals.flatMap fun w => keyParts.map fun x => keyOfK x w go!"d"

/-- A write of one of `SetUp`'s puts, without its kind: a set-up key (`setupKeys`) with the value
`setup`. -/
def setupPutK (k v : GoString) : Prop := k ∈ setupKeys ∧ v = go!"setup"

instance (k v : GoString) : Decidable (setupPutK k v) := by unfold setupPutK; infer_instance

/-- **A repeat of a set-up put** (`SetupWrite(e)`, of the event's kind `put`, key `k` and value
`v`): a put of a set-up key with the value `setup` (`setupPutK`). -/
def setupWriteK (put : Bool) (k v : GoString) : Prop := put = true ∧ setupPutK k v

instance (put : Bool) (k v : GoString) : Decidable (setupWriteK put k v) := by
  unfold setupWriteK; infer_instance

/-- **The history's check** (`CheckHistory(evs, setupRev, endKey)` returns): every event above
the set-up's revision `setupRev` but of the key `endKey` and a repeat of a set-up put
(`setupWriteK`) is a write its key's principal was permitted. -/
def histOk (evs : List wev) (setupRev : w64) (endKey : GoString) : Prop :=
  ∀ e ∈ evs, sint.Z setupRev < sint.Z e.Rev' → e.Key' ≠ endKey →
    ¬ setupWriteK e.Put' e.Key' e.Val' → permittedK (writerK e.Key') e.Key'

/-- The revision of the last event in `[lo, hi)`, from `last` (`LastIn`'s loop). -/
def lastInFrom (last : w64) (evs : List wev) : w64 :=
  evs.foldl (fun l e => if inRangeK e.Key' then e.Rev' else l) last

/-- **The revision of the last event of `evs` in `[lo, hi)`** (`LastIn(evs)`), `0` if none. -/
def lastIn (evs : List wev) : w64 := lastInFrom (W64 0) evs

end checks

end authkv
end EtcdGrove
end Perennial
