/-
`Bucket.Get` (bbolt): its spec in bbolt's API (the frozen spec of 2026-11-03; the vocabulary in
`Spec/go_etcd_io/bbolt/Api.lean`, the decisions in `notes/bbolt-spec-decisions.md`). Proof:
`Proof/go_etcd_io/bbolt/Bucket__Get.lean` (unfinished until bbolt's invariants are designed).
-/
module

public import Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
/- Every bbolt spec is stated over OsFs's semantics (round 11, D22: the default `osFs_semantics`,
whose `pwrite` within one aligned OS page is all-or-nothing): the binder `∀ [HasExt osFsExt]` at
the head of each triple (a section variable is dropped from a definition that does not use it),
and in the signature of each vocabulary predicate, so that every statement carries it (checked
with `#check`). -/
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `b.Get(key)` of a current handle, any fraction of either kind of transaction (it only reads):
the value, valid while the transaction is live, or nil if absent. (Margin: a present key whose
value was put as nil also reads back nil; Go's `Get` cannot tell them apart.) -/
abbrev Bucket.Get.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (n : GoString) (m : BktData)
    (key : GoSlice) (kb : GoString) (dk : DFrac),
  {{ boltTx (GF := GF) tx γ q T ∗ boltBkt tx b n (T.gen n) ∗ key ↦*{dk} kb ∗ ⌜T.cur.lookup n = some m⌝ }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"Get")) (Val #key))
  {{ (v : GoSlice), RET #v; boltTx tx γ q T ∗ key ↦*{dk} kb ∗
      (match m.lookup kb with
       | none => iprop(⌜v = slice.nil⌝)
       | some vb => txBytes tx v vb) }}

end spec

end bbolt
end EtcdGrove
end Perennial
