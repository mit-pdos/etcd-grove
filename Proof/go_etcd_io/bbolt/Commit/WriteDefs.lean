/-
`tx.write()`'s vocabulary (U10c, `notes/bbolt-proof-plan.md`; moved out of `Tx__write.lean` so that
the proof's lemma modules can use it): the slots of the dirty pages' extents (`bufSlots`), a page's
chunk per slot (`pageChunk`), the dirty pages' premise (`bufsOK`) and the target slots' resources
(`wrSlots`).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- The slots of the extents of the pages `bufs` (each page's id and its overflow), in the map's
order. -/
def bufSlots (bufs : GMap w64 (List w8)) : List Nat :=
  bufs.toList.flatMap fun e => List.range' e.1.toNat (1 + pageOverflow e.2)

/-- The bytes `tx.write` puts in slot `id + j` of the page `pg` at `id`: its `j`-th 4096. -/
def pageChunk (pg : List w8) (j : Nat) : List w8 := (pg.drop (4096 * j)).take 4096

/-- The dirty pages are writable: each buffer's header names its id, its length is its extent's,
and its extent lies in `[2, lim)` slots (`lim · 4096` at most the file's size and the mapping's
length). -/
def bufsOK (bufs : GMap w64 (List w8)) (lim : Nat) : Prop :=
  ∀ id pg, bufs !! id = some pg → pageId pg = id.toNat ∧
    pg.length = 4096 * (1 + pageOverflow pg) ∧ 2 ≤ id.toNat ∧ id.toNat + (1 + pageOverflow pg) ≤ lim

end pure

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- The target slots `S` of a write at the mapping `b`, holding `wb`: their page-cache bytes
(whole, `osSlot`) and their mapped cells' client halves (any values). -/
def wrSlots (b : Loc) (p : GoString) (S : List Nat) (wb : Nat → List w8) : IProp GF :=
  iprop([∗list] s ∈ S, osSlot p s (wb s) ∗ ∃ vf, cellsR b (4096 * s) 4096 vf)

end res

end bbolt
end EtcdGrove
end Perennial
