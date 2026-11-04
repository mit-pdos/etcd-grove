/-
`tx.commitFreelist()` (U10c of `notes/bbolt-proof-plan.md`; design §3.11, Commit step 4, run only
when `!NoFreelistSync`): a buffer of `flCount fl` pages allocated (`tx.allocate`, from the
freelist or at the high-water mark, which then grows), the freelist written into it
(`freelist.Write`: the post-allocation freelist's ids), and `tx.meta.freelist` set to its id. On
an allocation error the transaction is rolled back (`tx.rollback()`) and done.

The spec is over the writer's working state (`wtxW`/`wdbW`, as `Tx.allocate`'s). The error path's
rollback needs `wtxEnd`; the caller's frame `F` supplies what the writer state lacks (the full
database, `rwlock`, the closed flag's half, the page tokens, the agreed state, the data's quarter,
the facts), stated as two entailments: for the state allocate leaves unchanged, and for a lost
mapping (`derefRel` and a re-base). On success `F` comes back.
-/
module

public import Spec.go_etcd_io.bbolt.Tx__allocate
public import Proof.go_etcd_io.bbolt.Commit.RollbackSpec
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__Write
public import Spec.go_etcd_io.bbolt.internal.freelist.Interface__EstimatedWritePageSize
public import Spec.go_etcd_io.bbolt.internal.common.Meta__SetFreelist
public import Spec.go_etcd_io.bbolt.internal.common.Page__Id

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- The pages `commitFreelist` allocates for the freelist `fl`:
`EstimatedWritePageSize() / pageSize + 1`. -/
def flCount (fl : FLPg) : Nat :=
  (16 + 8 * (fl.allIds.length + (if 0xFFFF ≤ fl.allIds.length then 1 else 0))) / 4096 + 1

/-- The freelist page `freelist.Write` leaves in an allocated buffer of `count` pages at `id`:
the header (id, `freelistPageFlag`, the count field, overflow `count - 1`), the count (when at
least `0xFFFF` ids), the sorted ids, zeros. -/
def flPageBytes (fl : FLPg) (id : w64) (count : Nat) : List w8 :=
  let n := fl.allIds.length
  let body := (if n < 0xFFFF then [] else encode (W64 (n : Int))) ++
    (sortPgids fl.allIds).flatMap encode
  encode (⟨id, W16 (freelistPageFlag : Int), W16 ((if n < 0xFFFF then n else 0xFFFF : Nat) : Int),
      W32 ((count - 1 : Nat) : Int)⟩ : Page) ++
    (body ++ List.replicate (count * 4096 - 16 - body.length) (W8 0))

/-- `X` with the freelist page `bs` in the buffer of page `id` and `tx.meta.freelist = id`. -/
def WX.setFlPage (X : WX) (id : w64) (bs : List w8) : WX :=
  { X with t := { X.t with
      bufs := X.t.bufs.insert id bs,
      mv := { X.t.mv with freelist' := id } } }

end pure

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`tx.commitFreelist()`** (see the file header): `allocate`'s premises (for `flCount w.fl`
pages; the freelist's ids fewer than `2^48`), the caller's frame `F` with the two rollback
entailments. On success: `allocate`'s result `X1`/`w1` (`allocRes`, the page `id` at `p`, the
high-water mark bumped when taken from it), with the freelist page `flPageBytes w1.fl id` in its
buffer and `tx.meta.freelist = id`; `F` back. On an error: rolled back, done. -/
abbrev Tx.commitFreelist.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (X : WX) (w : WDb) (F : IProp GF),
  X.t.mv.txid' = w.wtxid → X.t.mv.pgid'.toNat * 4096 ≤ mapLen w.ms →
  derefPre X → liveFresh X → liveReach X → w.fl.allIds.length < 2 ^ 48 →
  (F ∗ wtxW K tx r false X ∗ wdbW K tx X.v w ⊢ wtxEnd K tx r X (wLive X.v w.C) w) →
  (∀ (X' : WX) (w' : WDb), (∃ Xd b, derefRel X Xd ∧ X' = Xd.rebase b) → w'.C = w.C →
    w'.fl = w.fl →
    F ∗ wtxLost K tx r false X' ∗ wdbLost K tx X'.v w' ⊢
      wtxEnd K tx r X' (some X'.v, some (w'.C.txid + 1), false, false) w') →
  {{ F ∗ wtxW (GF := GF) K tx r false X ∗ wdbW K tx X.v w }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"commitFreelist")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ ∃ (X1 : WX) (w1 : WDb) (id : w64) (p : Loc),
        F ∗ wtxW K tx r false (X1.setFlPage id (flPageBytes w1.fl id (flCount w.fl))) ∗
        wdbW K tx X1.v w1 ∗
        ⌜allocRes X X1 w.fl w1.fl w.wtxid (flCount w.fl) p id ∧ w1.C = w.C ∧
          X1.t.mv.pgid'.toNat * 4096 ≤ mapLen w1.ms ∧ (w1 = w.withFl w1.fl ∨ wdbRemap w w1)⌝) ∨
      (⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err ∗ txDoneDef tx) }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- Not yet (U10c): `EstimatedWritePageSize` and `Write` need the freelist's `flPgOwn` out of
`wdbW` (`wdbLive`), `SetFreelist` and `Id` the meta copy's and the new buffer's header out of
`wtxW` (`wtxHeap`): access lemmas of the shared predicates. -/
theorem Tx.commitFreelist.wp_proof (hAlloc : Tx.allocate.spec (GF := GF) (hG := hG))
    (hRb : Tx.rollback.spec (GF := GF) (hG := hG))
    (hEst : internal.freelist.Interface.EstimatedWritePageSize.spec (GF := GF) (hG := hG))
    (hWrite : internal.freelist.Interface.Write.spec (GF := GF) (hG := hG))
    (hSet : internal.common.Meta.SetFreelist.spec (GF := GF) (hG := hG))
    (hId : internal.common.Page.Id.spec (GF := GF) (hG := hG)) :
    Tx.commitFreelist.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end bbolt
end EtcdGrove
end Perennial
