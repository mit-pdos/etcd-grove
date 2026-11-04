/-
`Cursor.keyValue` of a reader (bbolt, internal to U6 of `notes/bbolt-proof-plan.md`): the entry
the top of the stack names in its leaf page (a page reference), its key and value as slices of
the view or of persistent heap bytes. Proof: `Proof/go_etcd_io/bbolt/Cursor__keyValue_r.lean`.
-/
module

public import Proof.go_etcd_io.bbolt.Read.Src

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **The result of `keyValue` at index `i` of the leaf page `pg`**: entry `i`'s key (a non-nil
slice), value (each from a live source) and flags, or nil, nil, `0` past the end. -/
def rKV (v : View) (pg : List w8) (i : Nat) (k vl : GoSlice) (fl : w32) : IProp GF :=
  if i < pageCount pg then
    iprop(∃ ks vs : Src, ⌜k ≠ slice.nil ∧ ks ≠ Src.stale ∧ vs ≠ Src.stale ∧ fl = (leafElem pg i).flags'⌝ ∗
      srcOwn v k ks (leafKey pg i) ∗ srcOwn v vl vs (leafValue pg i))
  else iprop(⌜k = slice.nil ∧ vl = slice.nil ∧ fl = W32 0⌝)

/-- `c.keyValue()` of a reader's cursor in bucket `b` (value `bv`) whose top element `e` refers
to the leaf page `pg` at position `pid`. -/
abbrev Cursor.keyValue_r.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) (b : Loc) (dq : DFrac)
    (bv : List w8) (ibp pp c : Loc) (stk : GoSlice)
    (els : List elemRef) (e : elemRef) (pid : Nat) (pg : List w8),
  rPageAt v bv pp pid = some (e.page', pg) → e.node' = null → pageFlags pg = leafPageFlag →
  leafWF pg pg.length → 16 ≤ pg.length → 0 ≤ sint.Z e.index' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ rdTxK (GF := GF) K tx src q T v ∗
      rBktP v tx b dq bv ibp pp ∗ c ↦ Cursor.mk b stk ∗ stk ↦* (els ++ [e]) }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"keyValue")) (Val #()))
  {{ (k vl : GoSlice) (fl : w32), RET (PairV (PairV #k #vl) #fl); rdTxK K tx src q T v ∗
      rBktP v tx b dq bv ibp pp ∗ c ↦ Cursor.mk b stk ∗ stk ↦* (els ++ [e]) ∗
      rKV v pg (sint.Z e.index').toNat k vl fl }}

end spec

end bbolt
end EtcdGrove
end Perennial
