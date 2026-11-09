/-
`(*intervalNode).visit(iv, sentinel, nv)` (internal): the in-order visit of the subtree's entries
overlapping `iv`, pruning a right subtree whose `max` is at or below the query's begin, until `nv`
returns `false`.

**Proof sketch.** Recursion on the subtree; `Interval.Compare` at each node (and of `[begin, max)`
against the query); the visitor's contract (`nodeVisitorOk`) on each overlapping node, its `iv`
lent (`ownNodeH`).

**Changes** from `specs-ref`'s file: at a key kind `c` (was a key representation `K` with
its comparison contract); pure premises in the precondition.

**Margin.** Mirrors the code.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Adt

open Iris Iris.BI go_etcd_io.etcd.pkg.v3.adt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

def intervalNode.visit.spec : Prop :=
  ∀ (c : Cmp) (s : Loc) (dq : DFrac) (p x : Loc) (Tx : RbT Entry) (ivp : Loc) (dq' : DFrac)
    (vb ve : val) (db de : DFrac) (b e : GoString) (nv : GoFunc) (S : List Entry)
    (I J : List (Loc × Entry) → IProp GF) (acc : List (Loc × Entry)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ ⌜(IvSorted Tx.inorder) ∧ (List.Sublist (acc.map Prod.snd ++ stab (b, e) Tx.inorder) S) ∧ (((b = go!"" ∨ affLt b e) → acc.map Prod.snd ++ stab (b, e) Tx.inorder <+: S))⌝ ∗
      ownNode c s dq p x Tx ∗ ivp ↦{dq'} c.ivl vb ve ∗ keyAt c db vb b ∗ keyAt c de ve e ∗
      nodeVisitorOk c dq S (b = go!"" ∨ affLt b e) nv I J ∗ I acc }}
    (App (App (App (Val (x @!! go.GoType.PointerType intervalNode.ty @!! go!"visit"))
      (Val #ivp)) (Val #s)) (Val #nv))
  {{ (r : Bool), RET #r; ivp ↦{dq'} c.ivl vb ve ∗ keyAt c db vb b ∗ keyAt c de ve e ∗
      ∃ (ns : List Loc) (es : List Entry),
        ⌜List.Sublist es (stab (b, e) Tx.inorder) ∧
          ((b = go!"" ∨ affLt b e) →
            if r then es = stab (b, e) Tx.inorder
            else es <+: stab (b, e) Tx.inorder ∧ es ≠ [])⌝ ∗
        ownNodeH c s dq p x Tx ns es ∗ (if r then I else J) (acc ++ ns.zip es) }}

end spec

end Adt
end EtcdGrove
end Perennial
