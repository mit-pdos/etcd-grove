/-
Label selectors (`k8s.io/apimachinery`'s `metav1.LabelSelector` and `labels.Selector`, names only
here): the pure model of what a `LabelSelector` selects, and the ownership of one, which the
trust-boundary spec of `metav1.LabelSelectorAsSelector` is stated with. Lean-first; phase 4 of
`notes/k8s-daemonset-plan.md` (the listers' `GetPodDaemonSets`, `GetHistoryDaemonSets`).

* `SelV`: a selector's value: its `MatchLabels` map and `MatchExpressions` (`Req`: key, operator,
  values). `selMatch S L`: the labels `L` meet every `MatchLabels` pair and every requirement
  (`In`: present with one of the values; `NotIn`: absent or none of them; `Exists`: present;
  `DoesNotExist`: absent), as `labels.internalSelector.Matches` of the requirements
  `LabelSelectorAsSelector` builds; a `nil` selector (`none`) matches nothing (`labels.Nothing()`).
  `selEmpty`: `Empty()` of the selector built: `true` exactly for a non-`nil` selector with no
  pair and no requirement (`labels.Everything()`), `false` for `nil` (`labels.Nothing()`).
* `lsOwn ls S` (persistent): `ls` is `nil` (`S = none`) or a `*LabelSelector` whose fields hold
  `S` (read only).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.cacher.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace labels

open Iris Iris.BI k8s_io.apimachinery.pkg.apis.«meta».v1

section model
variable [GooseExts]

/-- A `LabelSelectorRequirement`'s value. -/
structure Req where
  key : GoString
  op : GoString
  vals : List GoString

/-- A `LabelSelector`'s value. -/
structure SelV where
  ml : GMap GoString GoString
  reqs : List Req

/-- A requirement on the labels `L`. -/
def reqMatch (r : Req) (L : GMap GoString GoString) : Prop :=
  if r.op = go!"In" then ∃ v, L !! r.key = some v ∧ v ∈ r.vals
  else if r.op = go!"NotIn" then ∀ v, L !! r.key = some v → v ∉ r.vals
  else if r.op = go!"Exists" then r.key ∈ L
  else if r.op = go!"DoesNotExist" then r.key ∉ L
  else False

/-- **What a selector selects** (`nil`: nothing). -/
def selMatch : Option SelV → GMap GoString GoString → Prop
  | none, _ => False
  | some S, L => (∀ k v, S.ml !! k = some v → L !! k = some v) ∧ ∀ r ∈ S.reqs, reqMatch r L

/-- **Whether `LabelSelectorAsSelector` accepts a non-`nil` selector** (an uninterpreted predicate,
part of the trust boundary: its `MatchExpressions` operators are `In`, `NotIn`, `Exists`,
`DoesNotExist` and `labels.NewRequirement` accepts every requirement: label key and value syntax,
value counts). A function of the selector's value only. -/
axiom reqsValid : SelV → Prop

/-- `LabelSelectorAsSelector` returns no error (`nil`: none). -/
def selValid : Option SelV → Prop
  | none => True
  | some S => reqsValid S

/-- **`Empty()` of the selector built**: no pair and no requirement (`nil`: `false`). -/
def selEmpty : Option SelV → Bool
  | none => false
  | some S => decide (GMap.size S.ml = 0 ∧ S.reqs = [])

end model

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The selector at `ls` holds `S`** (persistent, read only). -/
def lsOwn (ls : Loc) : Option SelV → IProp GF
  | none => iprop(⌜ls = null⌝)
  | some S => iprop(∃ (ml : Loc) (ex : GoSlice) (rs : List LabelSelectorRequirement),
      ls ↦□ (LabelSelector.mk ml ex) ∗
      (⌜ml = null ∧ GMap.size S.ml = 0⌝ ∨ ml ↦${DFrac.discard} S.ml) ∗
      ex ↦*{DFrac.discard} rs ∗ ⌜rs.length = S.reqs.length⌝ ∗
      [∗list] i ↦ r ∈ rs, ∃ (q : Req) (vals : List GoString), ⌜S.reqs[i]? = some q ∧
        r.Key' = q.key ∧ r.Operator' = q.op ∧ q.vals = vals⌝ ∗ r.Values' ↦*{DFrac.discard} vals)

instance lsOwn_persistent (ls : Loc) (S : Option SelV) : Persistent (lsOwn (GF := GF) ls S) := by
  cases S <;> unfold lsOwn <;> infer_instance

open Classical in
/-- **A built selector's contract** for `S`: `Empty()` returns `selEmpty S`, and `Matches` on a
`labels.Set` map holding `L` (read only) returns whether `S` selects `L`. -/
def selOk (sel : GoInterface) (S : Option SelV) : IProp GF :=
  iprop(∃ i : GoInterfaceOk, ⌜sel = interface.ok i⌝ ∗
    {{ True }} (App (Val #(methods i.ty go!"Empty" i.v)) (Val #())) {{ RET #(selEmpty S); True }} ∗
    □ (∀ (lm : Loc) (L : GMap GoString GoString), {{ lm ↦${DFrac.discard} L }}
        (App (Val #(methods i.ty go!"Matches" i.v))
          (Val #(interface.mkOk k8s_io.apimachinery.pkg.labels.Set'.ty #lm)))
        {{ RET #(decide (selMatch S L)); True }}))

instance selOk_persistent (sel : GoInterface) (S : Option SelV) :
    Persistent (selOk (GF := GF) sel S) := by
  unfold selOk; infer_instance

end defs

end labels
end EtcdGrove
end Perennial
