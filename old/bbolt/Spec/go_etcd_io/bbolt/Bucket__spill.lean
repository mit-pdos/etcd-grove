module
public import Spec.go_etcd_io.bbolt.node__spill
public import Proof.go_etcd_io.bbolt.Inlineable

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section defs
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]
variable [float_sem : go.FloatConvSemantics]

/-- A bucket `C` (at `c`) of the transaction `T` before its spill: clean, its keys those
`rebalance` leaves (`rblKeysB`, no deficient node), its opened buckets its entries, its nodes
a tree (`bktRanked`) with heights (`rblHt`: all leaves at one depth), balanced, unspilled and with their capacities (`K`), their leaves'
entries without a child page (`leafPg0`), every entry's key and value together at most 2^28 bytes, and
its split threshold at most the page size (`splitThr`: a float fact). -/
def bucketU (W : WView) (T : WTx) (K : Loc → Bool) (c : Loc) (C : BRec) : Prop :=
  bktClean W (uint.nat T.mv.pgid') c C ∧ (∃ bnd, rblKeysB W C bnd none) ∧ bktNested W T C ∧
  bktRanked C ∧ leafPg0 C ∧ rblHt W C ∧
  (∀ l r, C.ns !! l = some r → r.nv.unbalanced' = false ∧ r.nv.spilled' = false ∧ K l = false ∧
    ∀ w ∈ r.ws, w.key.length + w.value.length ≤ 2 ^ 28) ∧
  uint.Z (splitThr (W64 (W.ps : Int)) C.bv.FillPercent') ≤ W.ps

/-- A bucket is opened from one parent entry at most (the buckets' caches form a forest; bbolt's
`openBucket` makes a new bucket each time, cached once). -/
def bmUnique (T : WTx) : Prop :=
  ∀ b1 B1 n1 b2 B2 n2 c, T.bs !! b1 = some B1 → B1.bm !! n1 = some c → T.bs !! b2 = some B2 →
    B2.bm !! n2 = some c → b1 = b2 ∧ n1 = n2

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [float_sem : go.FloatConvSemantics]

/-- The old tree of a bucket (its root `ib`): its pages' tokens (none for an inline one). -/
def oldToks (γ : GName) (W : WView) (ib : internal.common.InBucket) : IProp GF :=
  if ib.root' = W64 0 then emp else pgToks γ (treePages W.pages (uint.nat ib.root'))

/-- `b.spill()` of the bucket `bl` (record `B`) during `Commit`'s spill (`spillR`, `spillG`),
the buckets reachable from it through the bucket caches `Bs` (`bktReach`) all unspilled
(`bucketU`), with their tokens (`bktToks`). First its opened buckets: an inlineable one is
freed and written inline (`Bucket.free`, `Bucket.write`), another spilled (recursively); one
that changed (a materialized root) gets its new value put into `b`'s leaf holding its entry
(`seek`, `node`, `put`: the entry is there, so no "misplaced bucket header" or "unexpected
bucket header flag" panic). Then its own nodes (`node.spill`), its root page the top's
(below the high-water mark: no panic). The result: the bucket unchanged (no materialized root:
its old tree's tokens, `oldToks`), or its new root page `pid` and its written tree. On an
error, what `Commit`'s rollback needs (`spillErr`). -/
abbrev Bucket.spill.spec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc) (txid : w64)
    (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) (bl : Loc) (B : BRec)
    (Bs : List Loc),
  I.FreeSpec → spillG (hG := hG) W txl txid T ρ F → bmUnique T → T.bs !! bl = some B → Bs.Nodup →
  (∀ c, c ∈ Bs ↔ bktReach T bl c) →
  (∀ c C, c ∈ Bs → T.bs !! c = some C → bucketU W T K c C) → W.ps < 2 ^ 20 → W.pages !! 0 = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ spillR I γd γ W txl txid T ρ F K ∗
      [∗list] c ∈ Bs, ∃ C, ⌜T.bs !! c = some C⌝ ∗ bktToks γ W C }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"spill")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = interface.nil⌝ ∗ ∃ (W' : WView) (T' : WTx) (ρ' : DBState) (F' : GMap Nat (List w8))
          (K' : Loc → Bool) (B' : BRec),
        spillR I γd γ W' txl txid T' ρ' F' K' ∗
        ⌜spillG (hG := hG) W' txl txid T' ρ' F' ∧ spillFrame T T' (· ∈ Bs) ∧ W'.pages = W.pages ∧
          T'.bs !! bl = some B' ∧ B'.bm = B.bm ∧
          (∀ c C C', T.bs !! c = some C → T'.bs !! c = some C' → C'.bm = C.bm) ∧
          (∀ c C' l, c ∉ Bs → T'.bs !! c = some C' → (C'.ns !! l).isSome → K' l = K l)⌝ ∗
        ((⌜B.bv.rootNode' = null ∧ B'.bv = B.bv ∧ B'.ib = B.ib⌝ ∗ oldToks γ W B.ib) ∨
         (∃ (pid : w64) (top : Loc) (Q : GMap Nat (List w8)),
           ⌜B'.bv = { B.bv with rootNode' := top } ∧ B'.ib = { B.ib with root' := pid } ∧
             top ≠ null ∧ pid ≠ W64 0 ∧ (T'.bufs !! pid).isSome ∧ Q ⊆ spillPages W' T' ∧
             ∃ rt, B'.ns !! top = some rt ∧ rt.nv.pgid' = pid ∧ rt.nv.spilled' = true ∧
               rt.nv.parent' = null ∧ rt.cs = []⌝ ∗
           wtreeQ γ Q (uint.nat pid) none none))) ∨
      (⌜err ≠ interface.nil⌝ ∗ spillErr I γd txl txid) }}

end spec

end bbolt
end EtcdGrove
end Perennial
