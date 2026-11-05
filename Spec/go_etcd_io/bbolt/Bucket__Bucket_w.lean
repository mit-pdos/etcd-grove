/-
`Bucket.Bucket_w` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U6; used by U7 (`CreateBucket*`, `DeleteBucket`). Proof:
`Proof/go_etcd_io/bbolt/Bucket__Bucket_w.lean` (a `sorry` until U6).
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

/-- `b.Bucket(name)` of a writer (design §4.2 row 3): the cached child `name` if there is one;
else, if the searchable bucket `bl` has a nested bucket entry `name`, the child opened from its
value (`bktOpened`: cached in `b.buckets`, its handle registered at generation `g`), else nil. A
well-formed `X` stays so, with the same data. The name is a key (`keyR`: caller-owned at a
fraction, or bytes of the base view), given back; a child is returned with its handle's
persistent fragment `(name, g)` (a cached child's from the handles' fragments `hdlFrags`, whose
entry is `(name, g)` by the premise: for the root bucket, `gensOK` at `g = T.gen name`), and the
fragments are kept (maintainer R's U6g item 4). -/
abbrev Bucket.Bucket_w.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec) (name : GoSlice)
    (nb : List w8) (kr : KeyR) (g : Nat),
  X.t.bs !! bl = some B → bktLocalOK X bl → pmFresh X →
  X.t.t.writable' = true → (∀ c, B.bm !! nb = some c → X.handles !! c = some (nb, g)) →
  {{ wtxW (GF := GF) K tx r m X ∗ keyR X.v name kr nb ∗ hdlFrags r X.handles }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"Bucket")) (Val #name))
  {{ (c : Loc), RET #c; ∃ X' : WX, wtxW K tx r m X' ∗ keyR X.v name kr nb ∗
      hdlFrags r X'.handles ∗ (⌜c = null⌝ ∨ c ↪[r.n.bk]□ (nb, g)) ∗
      ⌜(c = null ∧ X' = X ∧ ¬ ∃ w ∈ X.allEnts bl, w.key = nb ∧ isBktFlag w.flags) ∨
       (c ≠ null ∧ ((B.bm !! nb = some c ∧ X' = X) ∨ bktOpened X X' bl c nb g) ∧
         (wOK X → wOK X' ∧ wtxData X' = wtxData X))⌝ }}

end spec

end bbolt
end EtcdGrove
end Perennial
