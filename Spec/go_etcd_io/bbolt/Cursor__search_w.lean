/-
`Cursor.search` of the writer (bbolt, internal to U6d of `notes/bbolt-proof-plan.md`): from a
searchable position `pid` of a searchable bucket (`posOK`), the stack grows by a logical path
routing the key (`lPathFrom`, `lRoutes`). Proof: `Proof/go_etcd_io/bbolt/Cursor__search_w.lean`.
-/
module

public import Proof.go_etcd_io.bbolt.Read.WKey

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

/-- `c.search(key, pid)` in the writer's searchable bucket `bl` (record `B`) from its searchable
position `pid` (position `0` of an inline bucket): the stack grows by a logical path from `pid`
routing `kb`, through searchable positions. Nothing of `X` changes. -/
abbrev Cursor.search_w.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec) (c : Loc)
    (stk : GoSlice) (els : List elemRef) (pid : w64) (key : GoSlice) (kr : KeyR) (kb : List w8),
  X.t.bs !! bl = some B → bktLocalOK X bl → pmFresh X → inlSrcOK X bl →
  posOK X bl B pid → (B.ib.root' = W64 0 → pid = W64 0) →
  {{ wtxW (GF := GF) K tx r m X ∗ c ↦ Cursor.mk bl stk ∗ stk ↦* els ∗
      ownSliceCap elemRef stk (DFrac.own 1) ∗ keyR X.v key kr kb }}
    (App (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"search")) (Val #key)) (Val #pid))
  {{ RET #(); ∃ (stk' : GoSlice) (path : List elemRef) (pids : List w64),
      wtxW K tx r m X ∗ c ↦ Cursor.mk bl stk' ∗ stk' ↦* (els ++ path) ∗
      ownSliceCap elemRef stk' (DFrac.own 1) ∗ keyR X.v key kr kb ∗
      ⌜lPathFrom X bl pid path pids ∧ lRoutes X bl path pids kb ∧ ∀ p ∈ pids, posOK X bl B p⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
