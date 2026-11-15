/-
Lean-first (no Rocq counterpart).

# The driver's selectors and attributes, as sets (stage 7e-2, `notes/k8s-7e-2-draft.md` §6)

What `getAttrs(o)` returns (`labMapL o`: `objLabels(o)`, the `app` label if not empty; `fldMapL o`:
the name, the namespace and the node) and what the driver's `labelSel.Matches`/`fieldSel.Matches`
answer on a set (`lmL s M`, `fmL s M`); on `getAttrs`' sets they are `KList`'s `labelSelOk` and
`fieldSelOk` (`lmL_labMapL`, `fmL_fldMapL`), so a predicate of the driver selects by `selOkL`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.KList
public import Proof.k8s_io.apiserver.pkg.storage.SelDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input labelSel fieldSel)

section go
variable [GooseExts]

/-- `objLabels(o)`'s set: `{"app": o.App}`, empty if the app is empty. -/
def labMapL (o : Obj) : GMap GoString GoString :=
  if o.App' = [] then ∅ else GMap.insert go!"app" o.App' ∅

/-- `getAttrs(o)`'s field set. -/
def fldMapL (o : Obj) : GMap GoString GoString :=
  GMap.insert go!"spec.nodeName" o.Node' (GMap.insert go!"metadata.namespace" o.Namespace'
    (GMap.insert go!"metadata.name" o.Name' ∅))

/-- `labelSel.Matches` on a set holding `M`. -/
def lmL (s : labelSel) (M : GMap GoString GoString) : Bool :=
  s.all' || ((M.lookup go!"app").isSome && decide ((M.lookup go!"app").getD [] = s.app'))

/-- `fieldSel.Matches` on a set holding `M`. -/
def fmL (s : fieldSel) (M : GMap GoString GoString) : Bool :=
  ((!decide (1 ≤ sint.Z s.n')) || decide ((M.lookup s.f1').getD [] = s.v1')) &&
    ((!decide (2 ≤ sint.Z s.n')) || decide ((M.lookup s.f2').getD [] = s.v2'))

/-- On `getAttrs`' labels, `labelSel.Matches` is `KList`'s `labelSelOk`. -/
theorem lmL_labMapL (s : labelSel) (o : Obj) : lmL s (labMapL o) = labelSelOk s o := by
  unfold lmL labMapL labelSelOk
  by_cases h : o.App' = []
  · simp [h]
  · simp [h, eq_comm]

/-- `getAttrs`' fields read as `objField`. -/
theorem fldMapL_lookup (o : Obj) (f : GoString) :
    ((fldMapL o).lookup f).getD [] = objField o f := by
  unfold fldMapL objField
  by_cases h1 : f = go!"metadata.name"
  · subst h1; simp
  by_cases h2 : f = go!"metadata.namespace"
  · subst h2; simp
  by_cases h3 : f = go!"spec.nodeName"
  · subst h3; simp
  simp [h1, h2, h3, Ne.symm h1, Ne.symm h2, Ne.symm h3]

/-- On `getAttrs`' fields, `fieldSel.Matches` is `KList`'s `fieldSelOk`. -/
theorem fmL_fldMapL (s : fieldSel) (o : Obj) : fmL s (fldMapL o) = fieldSelOk s o := by
  unfold fmL fieldSelOk
  rw [fldMapL_lookup, fldMapL_lookup]

end go

end k8s_etcd3
end EtcdGrove
end Perennial
