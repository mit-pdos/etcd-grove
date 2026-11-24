/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Proto/Model.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

The pure model of Gryff's register protocol (stage 1, one key), which Gryff's invariant
(`GryffProof/Proto/Inv.lean`) is stated over.

* Tags (carstamps) `(ts, cid, rmwc)` as integers (the Go fields' signed values), ordered
  lexicographically as `gryffproto.Tag.Compare` does (`tagLt`).
* The frontier of three replicas' stores: the median tag (`median3`): a tag is on a quorum (two of
  three replicas hold it or a greater one) iff it is at most the median.
* Operations: a client operation is named by `(client id, request id)` (`OpId`); its input is a
  read, a write of `v`, or a compare-and-swap; a write's and an RMW's tag is unique to it
  (`producer`), a read is placed after the write or RMW of the tag it returns.
* The RMW execution chain (`execOk`): the i-th executed RMW applies to the newer of its base and
  the previous result, and its result's tag is that tag with `rmwc + 1` (G1).
-/
module

public import Perennial.Std.Word

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.proto

/-- A tag (carstamp): `(ts, cid, rmwc)`. -/
abbrev PTag := Int × Int × Int

def tag0 : PTag := (0, 0, 0)

/-- `a < b` as `gryffproto.Tag.Compare` orders tags (lexicographic). -/
def tagLt (a b : PTag) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧ a.2.2 < b.2.2)))

def tagLe (a b : PTag) : Prop := tagLt a b ∨ a = b

instance (a b : PTag) : Decidable (tagLt a b) := by unfold tagLt; infer_instance
instance (a b : PTag) : Decidable (tagLe a b) := by unfold tagLe; infer_instance

def tagMax (a b : PTag) : PTag := if tagLt a b then b else a

/-- The median of three tags: the greatest tag that two of them reach. -/
def median3 (a b c : PTag) : PTag :=
  tagMax (if tagLt a b then a else b) (if tagLt (tagMax a b) c then tagMax a b else c)

/-- An RMW's result tag from the tag it applies to (G1). -/
def rmwTag (t : PTag) : PTag := (t.1, t.2.1, t.2.2 + 1)

/-- A client operation's name: (Gryff client id, request id). -/
abbrev OpId := Int × Int

/-- A client operation's input. -/
inductive OpIn where
  | read
  | write (v : Int)
  | cas (old new : Int)
deriving DecidableEq

/-- The value a compare-and-swap leaves. -/
def casStep (old new cur : Int) : Int := if cur = old then new else cur

/-- One executed RMW: its instance `(leader, slot)`, base `(value, tag)`, the CAS, and its result. -/
structure ExecEntry where
  inst : Int × Int
  base : Int × PTag
  old : Int
  new : Int
  res : Int × PTag

/-- The chain of executed RMWs is the executor's (with G1): each applies to the newer of its base
and the previous result, and its result's tag is that tag's `rmwTag`. `prev` is the previous
result (none before the first). -/
def execOk : Option (Int × PTag) → List ExecEntry → Prop
  | _, [] => True
  | prev, e :: es =>
    let cur := match prev with
      | none => e.base
      | some p => if tagLt p.2 e.base.2 then e.base else p
    e.res = (casStep e.old e.new cur.1, rmwTag cur.2) ∧ execOk (some e.res) es

end Perennial.gryff.proto
