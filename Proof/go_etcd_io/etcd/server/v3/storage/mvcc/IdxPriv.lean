/-
**The index during the rebuild** (the restore plan, R3's design point): a tree index no one
else can reach, its `RWMutex` private memory (`PlainRWMutex.lean`), its tree and key indexes
owned (`ownTree` at `1`). `restoreIntoIndex`'s goroutine owns it while it rebuilds the index and
calls `put`/`tombstone` on cached key indexes outside the tree's lock; `store.restore` turns it
into a lock-protected `isTreeIndex` (`init_RWMutex`) once the goroutine is done. Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvIndex
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.PlainRWMutex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

namespace mvcc

/-- Inserting an item equivalent to none of the items: a permutation of the item put in front. -/
theorem btInsert_perm_of_new {V : Type} {less : V → V → Prop} [DecidableRel less] (v : V) :
    ∀ (L : List V), (∀ w ∈ L, less w v ∨ less v w) → (btInsert less v L).Perm (v :: L)
  | [], _ => List.Perm.refl _
  | w :: ws, h => by
    unfold btInsert
    by_cases h1 : less w v
    · rw [ite_eq_left h1]
      have ih := btInsert_perm_of_new v ws (fun w' hw' => h w' (List.mem_cons_of_mem _ hw'))
      exact (List.Perm.cons w ih).trans (List.Perm.swap v w ws)
    · rw [ite_eq_right h1]
      have h2 : less v w := (h w List.mem_cons_self).resolve_left h1
      rw [ite_eq_left h2]

section reprs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **A tree index no one else can reach**, holding the entries `L`: its tree and logger (as
`isTreeIndex`), its `RWMutex` unlocked private memory, the tree and its key indexes owned. -/
def ownIdxPriv (ti : Loc) (L : List IdxEntry) : IProp GF :=
  iprop(∃ (t lg : Loc), ti.[treeIndex, go!"tree"] ↦□ t ∗ ti.[treeIndex, go!"lg"] ↦□ lg ∗
    ⌜lg ≠ null⌝ ∗ idxMuAddr ti ↦ rwZero ∗ ownTree t L 1)

end reprs

end mvcc

end EtcdGrove
end Perennial
