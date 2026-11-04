/-
`Bucket.Bucket_r` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U6; used by U10 (`tx_check` in `freepages`). Proof:
`Proof/go_etcd_io/bbolt/Bucket__Bucket_r.lean` (a `sorry` until U6).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Proof.go_etcd_io.bbolt.Read.RCtx

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

/-- `b.Bucket(name)` of a reader's bucket `b` (the root bucket, or a top-level one; its header
at `ibp`, its inline page at `pp`, `rBktP`, which it keeps):
the nested bucket `name`, opened from its value `cv` (persistent: a reader never writes it), or
nil if there is none. -/
abbrev Bucket.Bucket_r.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) (b : Loc) (dq : DFrac)
    (bv : List w8) (ibp pp : Loc) (name : GoSlice) (nb : List w8) (ks : Src),
  (bv = rootVal v ∨ ∃ n, (n, bv) ∈ treeEntries v.pages v.root) → ks ≠ Src.stale →
  {{ rdTxK (GF := GF) K tx src q T v ∗ rBktP v tx b dq bv ibp pp ∗ srcOwn v name ks nb }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"Bucket")) (Val #name))
  {{ (c : Loc), RET #c; rdTxK K tx src q T v ∗ rBktP v tx b dq bv ibp pp ∗
      ((⌜c = null ∧ nb ∉ bktNames v.pages bv⌝) ∨
       (∃ cv : List w8, ⌜c ≠ null ∧ bktEntry v.pages bv nb cv⌝ ∗ rBkt v tx c DFrac.discard cv)) }}

end spec

end bbolt
end EtcdGrove
end Perennial
