/-
`tx.commitFreelist()`'s vocabulary and lemmas (U10c, `notes/bbolt-proof-plan.md`): the pages it
allocates (`flCount`), the page `freelist.Write` leaves (`flPageBytes`, its length:
`flPageBytes_length`; `flPage_eq`), room for the post-allocation freelist (`flCount_room`,
`alloc_allIds_le`), the allocated buffer's lookups (`addPage_lookups`) and `tx.db` out of `wtxW`
(`wtxW_db_acc`).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.WAccess
public import Proof.go_etcd_io.bbolt.Commit.WritePage
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Model

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

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The writer's `tx.db` field out of `wtxW` and back, with its persistent facts. -/
theorem wtxW_db_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢
      (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ K.core ∗ ⌜r.db = K.db⌝) ∗
      tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} K.db ∗
      (tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} K.db -∗ wtxW K tx r m X) := by
  unfold wtxW wtxCore
  iintro ⟨⟨#Hpkg, #Hcore, %Hc, #Hreg, Hheap, Hfills, Hbk, Hnl, Hdb, Hvo, Hst⟩, Hvc, Hmap⟩
  have hdb : r.db = K.db := Hc.1
  isplitr
  · iframe #; ipureintro; exact hdb
  ihave Hdb' : tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} K.db $$ [Hdb]
  · rw [← hdb]; iexact Hdb
  iframe Hdb'
  iintro Hdb'
  ihave Hdb : tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} r.db $$ [Hdb']
  · rw [hdb]; iexact Hdb'
  iframe
  iframe #
  ipureintro; exact Hc

omit [GooseSemantics] [GooseInterp] go_gctx hos sem package_sem in
theorem addPage_lookups (X : WX) (id : w64) (p : Loc) (cnt : Nat) (h : w64) :
    (X.addPage id p cnt h).t.pm !! id = some p ∧
    (X.addPage id p cnt h).t.bufs !! id = some
      (encode (⟨id, W16 0, W16 0, W32 ((cnt - 1 : Nat) : Int)⟩ : Page) ++
        List.replicate (cnt * 4096 - 16) (W8 0)) :=
  ⟨GMap.lookup_insert _ _ _, GMap.lookup_insert _ _ _⟩

omit [GooseSemantics] [GooseInterp] go_gctx hos sem package_sem in
theorem alloc_allIds_le (fl : FLPg) (t r : w64) (n : Nat) :
    (fl.alloc t r n).allIds.length ≤ fl.allIds.length := by
  apply List.Sublist.length_le
  simp only [FLPg.allIds, FLPg.alloc, FLPg.pendingIds]
  exact List.Sublist.append List.filter_sublist (List.Sublist.refl _)

omit [GooseSemantics] [GooseInterp] go_gctx hos sem package_sem in
theorem flCount_room (n m : Nat) (hm : m ≤ n) :
    8 * (m + 1) ≤ ((16 + 8 * (n + (if 0xFFFF ≤ n then 1 else 0))) / 4096 + 1) * 4096 - 16 := by
  split <;> omega

omit [GooseSemantics] [GooseInterp] go_gctx hos sem package_sem in
/-- `freelist.Write`'s page is `flPageBytes`. -/
theorem flPage_eq (fl : FLPg) (id : w64) (cnt : Nat) :
    let n := fl.allIds.length
    let body := (if n < 0xFFFF then [] else encode (W64 (n : Int))) ++
      (sortPgids fl.allIds).flatMap encode
    encode (⟨id, W16 (freelistPageFlag : Int),
        W16 ((if n < 0xFFFF then n else 0xFFFF : Nat) : Int), W32 ((cnt - 1 : Nat) : Int)⟩ : Page) ++
      (body ++ List.replicate (cnt * 4096 - 16 - body.length) (W8 0)) = flPageBytes fl id cnt := rfl

omit [GooseSemantics] [GooseInterp] go_gctx hos sem package_sem in
theorem flPageBytes_length (fl : FLPg) (id : w64) (cnt : Nat)
    (h : 8 * (fl.allIds.length + 1) ≤ cnt * 4096 - 16) :
    (flPageBytes fl id cnt).length = cnt * 4096 := by
  have hb : ((if fl.allIds.length < 0xFFFF then [] else encode (W64 (fl.allIds.length : Int))) ++
      (sortPgids fl.allIds).flatMap encode).length ≤ 8 * (fl.allIds.length + 1) := by
    have hg : ∀ l : List w64, (l.flatMap (encode : w64 → List w8)).length = 8 * l.length := by
      intro l
      induction l with
      | nil => simp
      | cons x xs ih => simp only [List.flatMap_cons, List.length_append, ih,
          ByteEncoding.encode_length, List.length_cons]; omega
    have h1 : ((sortPgids fl.allIds).flatMap (encode : w64 → List w8)).length =
        8 * fl.allIds.length := by
      rw [hg, (sortPgids_perm fl.allIds).length_eq]
    rw [List.length_append, h1]
    split <;> simp [ByteEncoding.encode_length] <;> omega
  unfold flPageBytes
  simp only [List.length_append, ByteEncoding.encode_length, List.length_replicate] at hb ⊢
  omega

end proof

end bbolt
end EtcdGrove
end Perennial
