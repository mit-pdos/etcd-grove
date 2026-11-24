/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLc/Defs.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-c: definitions for F1 (`lin_replay`): an RMW's execution result (`rmwRes`, whose tag is its
place), producers' values (`pv`), the producer relation `Prod` (L3's conclusion for a carried pair
`(v, t)`), and the valuation `val l k` of tags at cut `k` (the value of the producer in `lin l k`
placed at the tag, 0 if none).
-/
module

public import Dsverify.Proof.gryff.Pure.LinDefs
public import Dsverify.Proof.gryff.PureLc.Replay

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure

open model kahn proto

/-- The result `(v, t)` of replica `r`'s first execution, with a command, of instance `x` in `es`
(`execTag` with the value). -/
noncomputable def execVT (r : Fin 3) (es : List Ev) (x : w32 × w32) : Option ValTag :=
  (List.range es.length).findSome? fun j =>
    match es[j]? with
    | some (Ev.exec q i) => if (q, i) = x then execRes (outsOf r es j) else none
    | _ => none

/-- An RMW's execution result: at the first replica (in id order) that executed its instance with
a command (`rmwPlace` with the value). -/
noncomputable def rmwRes (l : List Label) (o : Op) : Option ValTag :=
  (List.finRange 3).findSome? fun r => execVT r (projR l r) (rmwInst l o)

/-- An operation's place as a `PTag` (`tag0` if unplaced; `opLe`'s key). -/
noncomputable def pl (l : List Label) (o : Op) : PTag := ((place l o).map model.Tag.toP).getD proto.tag0

/-- A producer's value: a write's value, an RMW's result value. -/
noncomputable def pv (l : List Label) (o : Op) : w64 :=
  match o.inp with
  | .write v => v
  | .cas _ _ => ((rmwRes l o).map ValTag.v).getD 0
  | .read => 0

/-- **L3's conclusion** for a pair `(v, t)`: it is `(0, tag0)`, or a write's value at its place, or
an RMW's result. -/
def Prod (l : List Label) (v : w64) (t : model.Tag) : Prop :=
  (t.toP = proto.tag0 ∧ v = 0) ∨
  (∃ o ∈ ops l, o.inp = .write v ∧ place l o = some t) ∨
  (∃ o ∈ ops l, ∃ a b, o.inp = .cas a b ∧ rmwRes l o = some ⟨v, t⟩)

open Classical in
/-- The valuation of tags at cut `k`: the value of the producer in `lin l k` placed at `t`. -/
noncomputable def val (l : List Label) (k : Nat) (t : PTag) : w64 :=
  if h : ∃ o ∈ lin l k, o.rank = 0 ∧ pl l o = t then pv l h.choose else 0

end Perennial.gryff.pure
