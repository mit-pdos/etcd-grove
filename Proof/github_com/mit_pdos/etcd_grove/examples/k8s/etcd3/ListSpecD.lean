/-
Lean-first (no Rocq counterpart).

# The driver's list objects (`ListSpec`, stage 7e-2, `notes/k8s-7e-2-draft.md` §6)

`driverListSpec`: the list type `*ObjList`, its `Items` field, the items (each `Obj` the driver's
object `o` at some resource version `n`, its resource version string `rvStr n`; the slice owned
with its capacity), and the list's metadata (`ResourceVersion`, `Continue`,
`RemainingItemCount`). The Draft's `os = vs.map (objBody, rvString)` is filled as a pointwise
relation (`itemRelD`): an `Obj` is a `DObj` only with its fit.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjSpec
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ListDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProofMode k8s

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- An item of a list: the driver's object `x.1` at a resource version whose string is `x.2`. -/
def itemRelD (x : DObj × GoString) (v : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj) :
    Prop :=
  ∃ n : w64, v = x.1.toObj n ∧ x.2 = rvStr n

/-- The items slice `s` holds the items `os`, with its capacity. -/
def itemsAtD (s : GoSlice) (os : List (DObj × GoString)) : IProp GF :=
  iprop(∃ vs : List github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj, s ↦* vs ∗
    ownSliceCap github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Obj s (DFrac.own 1) ∗
    ⌜List.Forall₂ itemRelD os vs⌝)

theorem itemsAtD_nil : ⊢ itemsAtD (GF := GF) slice.nil [] := by
  unfold itemsAtD
  iexists []
  isplitl []
  · iapply ownSlice_nil
  isplitl []
  · iapply ownSliceCap_nil
  ipureintro; exact List.Forall₂.nil

theorem itemsAtD_len (s : GoSlice) (os : List (DObj × GoString)) :
    itemsAtD (GF := GF) s os ⊢ ⌜uint.nat s.len = os.length⌝ := by
  unfold itemsAtD
  iintro ⟨%vs, Hs, -, %Hf⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hs
  ipureintro
  rw [Hf.length_eq, Hl.1]
  have := Hl.2
  word

theorem itemsAtD_wf (s : GoSlice) (os : List (DObj × GoString)) :
    itemsAtD (GF := GF) s os ⊢ ⌜0 ≤ sint.Z s.len ∧ sint.Z s.len ≤ sint.Z s.cap⌝ := by
  unfold itemsAtD
  iintro ⟨%vs, -, Hc, -⟩
  iapply ownSliceCap_wf $$ Hc

/-- The list's metadata at `pl`. -/
def metaAtD (pl : Loc) (rv : w64) (cont : GoString) (rem : Option w64) : IProp GF :=
  iprop(structFieldRef github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList go!"ResourceVersion"
      pl ↦ rv ∗
    structFieldRef github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList go!"Continue" pl ↦ cont ∗
    ∃ r : Loc, structFieldRef github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList
      go!"RemainingItemCount" pl ↦ r ∗ remIs r rem)

/-- **The driver's list objects** (see the file header). -/
def driverListSpec : ListSpec GF DObj where
  listTy := github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList.ty
  itemsRef pl := structFieldRef github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.ObjList go!"Items" pl
  itemsAt := itemsAtD
  itemsAt_nil := itemsAtD_nil
  itemsAt_len := itemsAtD_len
  itemsAt_wf := itemsAtD_wf
  metaAt := metaAtD

end defs

end k8s_etcd3
end EtcdGrove
end Perennial
