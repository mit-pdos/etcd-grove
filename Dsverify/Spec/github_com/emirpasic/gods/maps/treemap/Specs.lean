/-
**gods' treemap** (`github.com/emirpasic/gods/maps/treemap`, v1.18.1): the specs of the functions
the kits call, one set shared by them (SwiftPaxos's `state`: `NewWith`, `Put`, `Get`; EPaxos's
`state`: those and, for `SCAN`, `Select`, `Iterator`, `Iterator.Next`, `Iterator.Value`).

The translated gods (`Dsverify/Code/github_com/emirpasic/gods/**`) is real, but nothing proves it
here (its red-black tree iterator's `Next`/`Prev` are names only: `goto`); the lab proved a cut-down
copy instead. So these specs are hypotheses, stated over abstract representation predicates (a kit
takes them as premises: SwiftPaxos's `SwiftHyps` over its `SwiftLibs.isTreeMap`, EPaxos's `Hyps`
below, from which it derives its `state.KeyComparator` specialization):

* `isTreeMap m enc es`: the `*Map` at `m` holds the entries `es` (`Defs.lean`: key, value
  interface, strictly increasing by signed key), its keys the interfaces `enc k`, its comparator
  one that meets `cmpOk cmp enc` (on two encoded keys, an `int` whose sign is the signed comparison
  of the keys);
* `iterVal v es`: the `Iterator` value `v` (`m.Iterator()`'s result) over the entries `es`, before
  its first `Next`; stored at `p`, it is `ownIter p es none` (`iter_alloc.law`);
* `ownIter p rest cur`: the iterator at `p`, at entry `cur` (`none` before the first `Next` and
  after the last), with `rest` still to visit.

Each spec is what gods' code does (`maps/treemap/treemap.go`, `enumerable.go`, `iterator.go`): the
map is a red-black tree ordered by its comparator, `Put` replaces the value of an equal key or
inserts, `Get` returns the value and `true` or `nil` and `false`, `Select` builds a new map with the
same comparator by `Put`ting each entry, in key order, on which `f` answers `true`, and an iterator
visits the entries in key order.
-/
module

public import Dsverify.Proof.github_com.emirpasic.gods.maps.treemap.Defs
public import Dsverify.Proof.github_com.emirpasic.gods.maps.treemap.Base
public import Perennial.Golang.Theory

@[expose] public section

noncomputable section

namespace Perennial.github_com.emirpasic.gods.maps.treemap

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- The comparator `cmp` compares encoded keys as signed integers (persistent). -/
def cmpOk (cmp : GoFunc) (enc : w64 → GoInterface) : IProp GF :=
  iprop(□ ∀ (a b : w64) (Φ : val → IProp GF),
    ▷ (∀ c : w64, ⌜(sint.Z c < 0 ↔ sint.Z a < sint.Z b) ∧ (c = W64 0 ↔ a = b)⌝ -∗ Φ #c) -∗
    WP (App (App (Val #cmp) (Val #(enc a))) (Val #(enc b))) {{ Φ }})

instance cmpOk_persistent (cmp : GoFunc) (enc : w64 → GoInterface) :
    Persistent (cmpOk (GF := GF) cmp enc) := by unfold cmpOk; infer_instance

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [treemap.Assumptions]
variable (isTreeMap : Loc → (w64 → GoInterface) → Entries → IProp GF)
variable (iterVal : github_com.emirpasic.gods.maps.treemap.Iterator → Entries → IProp GF)
variable (ownIter : Loc → Entries → Option (w64 × GoInterface) → IProp GF)

/-- `NewWith(cmp)`, `cmp` comparing the keys `enc` encodes: an empty map. -/
abbrev NewWith.spec : Prop :=
  ∀ (cmp : GoFunc) (enc : w64 → GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.emirpasic.gods.maps.treemap ∗
      cmpOk cmp enc }}
    (App (Val (@! treemap.NewWith)) (Val #cmp))
  {{ (tm : Loc), RET #tm; isTreeMap tm enc [] }}

/-- `m.Put(key, value)`. -/
abbrev Map.Put.spec : Prop :=
  ∀ (tm : Loc) (enc : w64 → GoInterface) (es : Entries) (k : w64) (v : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.emirpasic.gods.maps.treemap ∗
      isTreeMap tm enc es }}
    (App (App (Val (tm @!! go.GoType.PointerType Map.ty @!! go!"Put")) (Val #(enc k))) (Val #v))
  {{ RET #(); isTreeMap tm enc (putE es k v) }}

/-- `m.Get(key)`: `key`'s value and `true`, or `nil` and `false`. -/
abbrev Map.Get.spec : Prop :=
  ∀ (tm : Loc) (enc : w64 → GoInterface) (es : Entries) (k : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.emirpasic.gods.maps.treemap ∗
      isTreeMap tm enc es }}
    (App (Val (tm @!! go.GoType.PointerType Map.ty @!! go!"Get")) (Val #(enc k)))
  {{ RET (PairV #((lookupE es k).getD interface.nil) #((lookupE es k).isSome));
      isTreeMap tm enc es }}

/-- `m.Select(f)`, `f` answering `P k` from `R` (keeping it) on each entry `(k, v)` of the map: a
new map of the entries whose keys satisfy `P`; `m` unchanged. -/
abbrev Map.Select.spec : Prop :=
  ∀ (tm : Loc) (enc : w64 → GoInterface) (es : Entries) (f : GoFunc) (P : w64 → Bool)
    (R : IProp GF),
    (∀ (k : w64) (v : GoInterface), (k, v) ∈ es →
      {{ R }} (App (App (Val #f) (Val #(enc k))) (Val #v)) {{ RET #(P k); R }}) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.emirpasic.gods.maps.treemap ∗
        isTreeMap tm enc es ∗ R }}
      (App (Val (tm @!! go.GoType.PointerType Map.ty @!! go!"Select")) (Val #f))
    {{ (tm' : Loc), RET #tm'; isTreeMap tm enc es ∗ R ∗
        isTreeMap tm' enc (es.filter (fun e => P e.1)) }}

/-- `m.Iterator()`: an iterator over the map's entries in key order (consuming the map's
representation). -/
abbrev Map.Iterator.spec : Prop :=
  ∀ (tm : Loc) (enc : w64 → GoInterface) (es : Entries),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.emirpasic.gods.maps.treemap ∗
        isTreeMap tm enc es }}
      (App (Val (tm @!! go.GoType.PointerType Map.ty @!! go!"Iterator")) (Val #()))
    {{ (v : github_com.emirpasic.gods.maps.treemap.Iterator), RET #v; iterVal v es }}

/-- An iterator value stored at `p` is the iterator at `p`, before its first entry. -/
abbrev iter_alloc.law : Prop :=
  ∀ (p : Loc) (v : github_com.emirpasic.gods.maps.treemap.Iterator) (es : Entries),
    p ↦ v ∗ iterVal v es ⊢ ownIter p es none

/-- `it.Next()`: the next entry, if any. -/
abbrev Iterator.Next.spec : Prop :=
  ∀ (p : Loc) (rest : Entries) (cur : Option (w64 × GoInterface)),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.emirpasic.gods.maps.treemap ∗
        ownIter p rest cur }}
      (App (Val (p @!! go.GoType.PointerType Iterator.ty @!! go!"Next")) (Val #()))
    {{ (b : Bool), RET #b;
        match rest with
        | [] => ⌜b = false⌝ ∗ ownIter p [] none
        | e :: r => ⌜b = true⌝ ∗ ownIter p r (some e) }}

/-- `it.Value()` at entry `(k, v)`: `v`. -/
abbrev Iterator.Value.spec : Prop :=
  ∀ (p : Loc) (rest : Entries) (k : w64) (v : GoInterface),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.emirpasic.gods.maps.treemap ∗
        ownIter p rest (some (k, v)) }}
      (App (Val (p @!! go.GoType.PointerType Iterator.ty @!! go!"Value")) (Val #()))
    {{ RET #v; ownIter p rest (some (k, v)) }}

end spec

/-- **The hypothesis** (the file header): gods' treemap's representation predicates and the specs
over them. -/
class Hyps [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] (GF : BundledGFunctors)
    [HeapGS HasLC.hasLC GF] [go.Semantics] [treemap.Assumptions] where
  isTreeMap : Loc → (w64 → GoInterface) → Entries → IProp GF
  iterVal : github_com.emirpasic.gods.maps.treemap.Iterator → Entries → IProp GF
  ownIter : Loc → Entries → Option (w64 × GoInterface) → IProp GF
  NewWith_spec : NewWith.spec (GF := GF) isTreeMap
  Put_spec : Map.Put.spec (GF := GF) isTreeMap
  Get_spec : Map.Get.spec (GF := GF) isTreeMap
  Select_spec : Map.Select.spec (GF := GF) isTreeMap
  Iterator_spec : Map.Iterator.spec (GF := GF) isTreeMap iterVal
  iter_alloc : iter_alloc.law (GF := GF) iterVal ownIter
  Next_spec : Iterator.Next.spec (GF := GF) ownIter
  Value_spec : Iterator.Value.spec (GF := GF) ownIter

end Perennial.github_com.emirpasic.gods.maps.treemap
