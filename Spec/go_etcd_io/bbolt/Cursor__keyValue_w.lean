/-
`Cursor.keyValue` of the writer (bbolt, internal to U6d of `notes/bbolt-proof-plan.md`): the entry
the top of the stack names in its leaf (a live node, or a page), its key and value as slices with
their sources (`leafSrc`). Proof: `Proof/go_etcd_io/bbolt/Cursor__keyValue_w.lean`.
-/
module

public import Proof.go_etcd_io.bbolt.Read.WCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **The result of the writer's `keyValue` at the leaf entries `ws`, index `i`**: the entry's key
(a non-nil slice), value and flags, with their sources (`leafSrc`), or nil, nil, `0` past the
end. -/
def wKV (X : WX) (bl : Loc) (ws : List WEntry) (i : Nat) (k vl : GoSlice) (fl : w32) : IProp GF :=
  match ws[i]? with
  | some w => iprop(⌜k ≠ slice.nil ∧ fl = w.flags⌝ ∗ srcOwn X.v k (leafSrc X bl w.ks) w.key ∗
      srcOwn X.v vl (leafSrc X bl w.vs) w.value)
  | none => iprop(⌜k = slice.nil ∧ vl = slice.nil ∧ fl = W32 0⌝)

/-- `c.keyValue()` of a writer's cursor in the searchable bucket `bl` whose top element `e` refers
to the leaf at the searchable position `pid` (entries `ws`). -/
abbrev Cursor.keyValue_w.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec) (c : Loc)
    (stk : GoSlice) (els : List elemRef) (e : elemRef) (pid : w64) (ws : List WEntry),
  X.t.bs !! bl = some B → bktLocalOK X bl → pmFresh X → inlSrcOK X bl → posOK X bl B pid →
  refAt X bl pid e → ltree X bl pid = some (true, ws) → 0 ≤ sint.Z e.index' →
  {{ wtxW (GF := GF) K tx r m X ∗ c ↦ Cursor.mk bl stk ∗ stk ↦* (els ++ [e]) }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"keyValue")) (Val #()))
  {{ (k vl : GoSlice) (fl : w32), RET (PairV (PairV #k #vl) #fl); wtxW K tx r m X ∗
      c ↦ Cursor.mk bl stk ∗ stk ↦* (els ++ [e]) ∗ wKV X bl ws (sint.Z e.index').toNat k vl fl }}

/-- **`keyValue` at a fraction** (U6w): `Cursor.keyValue_w.spec` over `wtxWQ` at any `q`, given
back unchanged. `spec` is its case `q = 1`. -/
abbrev Cursor.keyValue_w.specQ : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) (bl : Loc) (B : BRec) (c : Loc)
    (stk : GoSlice) (els : List elemRef) (e : elemRef) (pid : w64) (ws : List WEntry),
  X.t.bs !! bl = some B → bktLocalOK X bl → pmFresh X → inlSrcOK X bl → posOK X bl B pid →
  refAt X bl pid e → ltree X bl pid = some (true, ws) → 0 ≤ sint.Z e.index' →
  {{ wtxWQ (GF := GF) K tx r m q X ∗ c ↦ Cursor.mk bl stk ∗ stk ↦* (els ++ [e]) }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"keyValue")) (Val #()))
  {{ (k vl : GoSlice) (fl : w32), RET (PairV (PairV #k #vl) #fl); wtxWQ K tx r m q X ∗
      c ↦ Cursor.mk bl stk ∗ stk ↦* (els ++ [e]) ∗ wKV X bl ws (sint.Z e.index').toNat k vl fl }}

end spec

end bbolt
end EtcdGrove
end Perennial
