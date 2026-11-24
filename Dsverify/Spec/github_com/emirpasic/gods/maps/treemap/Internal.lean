/-
gods' treemap: the specs of the iterator methods with the iterated tree explicit
(`ownIterTM`, `Proof/.../maps/treemap/Rep.lean`), which `Select`'s proof uses (it gets its map
back after the walk), and of `Map.Iterator` on the map's points-to.
-/
module

public import Dsverify.Proof.github_com.emirpasic.gods.maps.treemap.Rep

@[expose] public section

noncomputable section

namespace Perennial.github_com.emirpasic.gods.maps.treemap

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.emirpasic.gods.trees.redblacktree (RB)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [treemap.Assumptions]

/-- `m.Iterator()`: before the first entry of `m`'s tree. -/
abbrev Map.IteratorT.spec : Prop :=
  ∀ (tm tr : Loc),
  {{ tm ↦ Map.mk tr }}
    (App (Val (tm @!! go.GoType.PointerType Map.ty @!! go!"Iterator")) (Val #()))
  {{ RET #(Iterator.mk (trees.redblacktree.Iterator.mk tr null (W8 0))); (tm ↦ Map.mk tr : IProp GF) }}

/-- `it.Next()`, the tree fixed. -/
abbrev Iterator.NextT.spec : Prop :=
  ∀ (p tr : Loc) (enc : w64 → GoInterface) (cmp : GoFunc) (T : RB GoInterface)
    (h : Loc → trees.redblacktree.Node) (D : List Loc) (rest : Entries)
    (cur : Option (w64 × GoInterface)),
  {{ ownIterTM (GF := GF) p tr enc cmp T h D rest cur }}
    (App (Val (p @!! go.GoType.PointerType Iterator.ty @!! go!"Next")) (Val #()))
  {{ (b : Bool), RET #b;
      match rest with
      | [] => ⌜b = false⌝ ∗ ownIterTM p tr enc cmp T h D [] none
      | e :: r => ⌜b = true⌝ ∗ ownIterTM p tr enc cmp T h D r (some e) }}

/-- `it.Value()` at `(k, v)`, the tree fixed. -/
abbrev Iterator.ValueT.spec : Prop :=
  ∀ (p tr : Loc) (enc : w64 → GoInterface) (cmp : GoFunc) (T : RB GoInterface)
    (h : Loc → trees.redblacktree.Node) (D : List Loc) (rest : Entries) (k : w64) (v : GoInterface),
  {{ ownIterTM (GF := GF) p tr enc cmp T h D rest (some (k, v)) }}
    (App (Val (p @!! go.GoType.PointerType Iterator.ty @!! go!"Value")) (Val #()))
  {{ RET #v; ownIterTM p tr enc cmp T h D rest (some (k, v)) }}

/-- `it.Key()` at `(k, v)`, the tree fixed. -/
abbrev Iterator.KeyT.spec : Prop :=
  ∀ (p tr : Loc) (enc : w64 → GoInterface) (cmp : GoFunc) (T : RB GoInterface)
    (h : Loc → trees.redblacktree.Node) (D : List Loc) (rest : Entries) (k : w64) (v : GoInterface),
  {{ ownIterTM (GF := GF) p tr enc cmp T h D rest (some (k, v)) }}
    (App (Val (p @!! go.GoType.PointerType Iterator.ty @!! go!"Key")) (Val #()))
  {{ RET #(enc k); ownIterTM p tr enc cmp T h D rest (some (k, v)) }}

end spec

end Perennial.github_com.emirpasic.gods.maps.treemap
