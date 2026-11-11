/-
Lean-first (no Rocq counterpart).

# What a `SelectionPredicate` selects (stage 7e-2, `notes/k8s-7e-2-draft.md` §4.3)

The selectors and the attribute function a predicate holds, as the `SelectionPredicate` methods
reach them:

- `mapRO m M`: a `labels.Set`/`fields.Set` value (a Go map) holding `M`, read-only: `nil` (`M`
  empty) or a map (`getAttrs`' fresh maps, persisted);
- `labelSelOk ls le lm`: the `labels.Selector` `ls` is not `nil`, its `Empty()` answers `le` and its
  `Matches(l)` on a set holding `M` (as a `labels.Labels`) answers `lm M`; `fieldSelOk` the same for a
  `fields.Selector` on a `fields.Set`;
- `getAttrsOk objAt ga lab fld`: the attribute function `ga` on an object `x` held as `objAt x o`
  returns sets holding `lab o` and `fld o`, and no error;
- `selPredOk S p sel emp`: the predicate `p` selects by `sel` and is empty iff `emp` (its `Matches`
  and `Empty` triples, for the store's objects `S.objAt`), no sharding.

The method specs are stated for any object predicate `objAt` (a form settled at Prove: the store
uses `S.objAt _ _ rv`, the driver's model `&o ↦{dq} o`).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Contract

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable {O : Type}

/-- A set (a Go map of strings) holding `M`, read-only: `nil` and empty, or a map. -/
def mapRO (m : Loc) (M : GMap GoString GoString) : IProp GF :=
  iprop(⌜m = map.nil ∧ M = ∅⌝ ∨ m ↦$□ M)

instance mapRO_persistent (m : Loc) (M : GMap GoString GoString) :
    Persistent (mapRO (GF := GF) m M) := by
  unfold mapRO; infer_instance

/-- **A label selector's `Empty`/`Matches`** (`labels.Selector`, on a `labels.Set` held at a map
pointer, as a `labels.Labels`) answer `le` and `lm` of the set's contents. -/
def labelSelOk (ls : GoInterface) (le : Bool) (lm : GMap GoString GoString → Bool) : IProp GF :=
  iprop(∃ ii : GoInterfaceOk, ⌜ls = GoInterface.ok ii⌝ ∗
    □ (∀ Φ : val → IProp GF, ▷ Φ #le -∗
        WP (App (Val #(methods ii.ty go!"Empty" ii.v)) (Val #())) {{ Φ }}) ∗
    □ (∀ (m : Loc) (M : GMap GoString GoString) (Φ : val → IProp GF), mapRO m M -∗ ▷ Φ #(lm M) -∗
        WP (App (Val #(methods ii.ty go!"Matches" ii.v))
          (Val #(interface.mkOk k8s_io.apimachinery.pkg.labels.Set'.ty #m))) {{ Φ }}))

/-- The same for a field selector (`fields.Selector` on a `fields.Set`). -/
def fieldSelOk (fs : GoInterface) (fe : Bool) (fm : GMap GoString GoString → Bool) : IProp GF :=
  iprop(∃ ii : GoInterfaceOk, ⌜fs = GoInterface.ok ii⌝ ∗
    □ (∀ Φ : val → IProp GF, ▷ Φ #fe -∗
        WP (App (Val #(methods ii.ty go!"Empty" ii.v)) (Val #())) {{ Φ }}) ∗
    □ (∀ (m : Loc) (M : GMap GoString GoString) (Φ : val → IProp GF), mapRO m M -∗ ▷ Φ #(fm M) -∗
        WP (App (Val #(methods ii.ty go!"Matches" ii.v))
          (Val #(interface.mkOk k8s_io.apimachinery.pkg.fields.Set'.ty #m))) {{ Φ }}))

/-- **`GetAttrs` on an object answers its label and field sets** (read-only), no error. -/
def getAttrsOk (objAt : GoInterface → O → IProp GF) (ga : GoFunc)
    (lab fld : O → GMap GoString GoString) : IProp GF :=
  iprop(□ ∀ (x : GoInterface) (o : O) (Φ : val → IProp GF), objAt x o -∗
    ▷ (∀ (lm fm : Loc), objAt x o -∗ mapRO lm (lab o) -∗ mapRO fm (fld o) -∗
        Φ (PairV (PairV #lm #fm) #GoInterface.nil)) -∗
    WP (App (Val #ga) (Val #x)) {{ Φ }})

instance labelSelOk_persistent ls le lm : Persistent (labelSelOk (GF := GF) ls le lm) := by
  unfold labelSelOk; infer_instance
instance fieldSelOk_persistent fs fe fm : Persistent (fieldSelOk (GF := GF) fs fe fm) := by
  unfold fieldSelOk; infer_instance
instance getAttrsOk_persistent (objAt : GoInterface → O → IProp GF) ga lab fld :
    Persistent (getAttrsOk objAt ga lab fld) := by
  unfold getAttrsOk; infer_instance

/-- **The predicate `p` selects by `sel`, and is empty iff `emp`** (persistent): `Matches` on an
object answers `sel` of its body, `Empty` answers `emp`; no sharding (a `nil` `ShardSelector`); an
empty predicate selects everything. -/
def selPredOk {Obj : Type} (S : ObjSpec GF Obj) (p : k8s_io.apiserver.pkg.storage.SelectionPredicate)
    (sel : Obj → Bool) (emp : Bool) : IProp GF :=
  iprop(⌜p.ShardSelector' = GoInterface.nil ∧ (emp = true → ∀ o, sel o = true)⌝ ∗
    □ (∀ (pp : Loc) (dq : DFrac) (x : GoInterface) (o : Obj) (rv : GoString) (Φ : val → IProp GF),
      pp ↦{dq} p -∗ S.objAt x o rv -∗
      ▷ (pp ↦{dq} p -∗ S.objAt x o rv -∗ Φ (PairV #(sel o) #GoInterface.nil)) -∗
      WP (App (Val (pp @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.SelectionPredicate.ty
        @!! go!"Matches")) (Val #x)) {{ Φ }}) ∗
    □ (∀ (pp : Loc) (dq : DFrac) (Φ : val → IProp GF),
      pp ↦{dq} p -∗ ▷ (pp ↦{dq} p -∗ Φ #emp) -∗
      WP (App (Val (pp @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.SelectionPredicate.ty
        @!! go!"Empty")) (Val #())) {{ Φ }}))

instance selPredOk_persistent {Obj : Type} (S : ObjSpec GF Obj) p sel emp :
    Persistent (selPredOk S p sel emp) := by
  unfold selPredOk; infer_instance

end defs

end k8s
end EtcdGrove
end Perennial
