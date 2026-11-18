/-
The Go values of the mvcc KV core's model (`Model.lean`): `mvcc.Revision` as `Rev`, and the
representation predicates of a key index (`keyIndex`, `generation`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Model

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section defs
variable [GooseExts] [GoGlobalContext]

/-- The Go `Revision` value of a model revision. -/
def revVal (r : Rev) : Revision := ⟨r.main, r.sub⟩

end defs

section addrs
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

end addrs

section inj
variable [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

end inj

/-! ## Key indexes (`key_index.go`) -/

section reprs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The Go `generation` value `gv` holds the model generation `gm`: its `ver` and `created`'s
main revision (`Gen`: its sub-revision is the field's own), and its revisions in the slice `revs` (at fraction `dq`, with the slice's capacity at the same
fraction: `put` appends to it). -/
def ownGen (gv : generation) (gm : Gen) (dq : DFrac) : IProp GF :=
  iprop(⌜gv.ver' = gm.ver ∧ gv.created'.Main' = gm.created⌝ ∗
    gv.revs' ↦*{dq} gm.revs.map revVal ∗ ownSliceCap Revision gv.revs' dq)

/-- The Go values `gvs` hold the model generations `gens`, in order. -/
def ownGensL (dq : DFrac) : List generation → List Gen → IProp GF
  | [], [] => iprop(True)
  | gv :: gvs, gm :: gens => iprop(ownGen gv gm dq ∗ ownGensL dq gvs gens)
  | [], _ :: _ => iprop(False)
  | _ :: _, [] => iprop(False)

/-- The generations slice `gs` holds the model generations `gens`, in order. -/
def ownGens (gs : GoSlice) (gens : List Gen) (dq : DFrac) : IProp GF :=
  iprop(∃ gvs : List generation,
    gs ↦*{dq} gvs ∗ ownSliceCap generation gs dq ∗ ownGensL dq gvs gens)

/-- `p` is a `*keyIndex` of key `k`, for good: the key is set by `&keyIndex{key: k}` and
never written. -/
def kiKey (p : Loc) (k : GoString) : IProp GF :=
  iprop(∃ ks : GoSlice, p.[keyIndex, go!"key"] ↦□ ks ∗ ks ↦*□ k)

/-- The mutable part of the `*keyIndex` `p`: `modified` and its generations slice `gs`
(`ownGens`), holding `ki`, at fraction `dq`. -/
def ownKi (p : Loc) (gs : GoSlice) (ki : KeyIndex) (dq : DFrac) : IProp GF :=
  iprop(p.[keyIndex, go!"modified"] ↦{dq} revVal ki.modified ∗
    p.[keyIndex, go!"generations"] ↦{dq} gs ∗ ownGens gs ki.gens dq)

/-- `Revision`s are compared by their fields (the `available` map's keys). -/
instance revision_decEq : DecidableEq Revision := fun a b =>
  if h : a.Main' = b.Main' ∧ a.Sub' = b.Sub' then
    isTrue (by cases a; cases b; simp only at h; rw [h.1, h.2])
  else isFalse (by intro e; subst e; exact h ⟨rfl, rfl⟩)

end reprs

end mvcc
end EtcdGrove
end Perennial
