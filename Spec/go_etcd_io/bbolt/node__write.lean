/-
`node.write` (bbolt, internal): its spec (U0b of `notes/bbolt-proof-plan.md`, a frozen
cross-unit contract). Proved by U9a; used by U9b (`Bucket.write`, `node.spill`). Proof:
`Proof/go_etcd_io/bbolt/node__write.lean` (a `sorry` until U9a).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx

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

/-- `n.write(p)` into an empty page (header `hdr` with no flags and no elements, then `R` zeroed
bytes): the header becomes a leaf's or a branch's (as the node) with the inodes' count, and the
inodes `ms` (their bytes read at `dqb`) are laid out after it (`pageBody`; nothing for an empty
node). It panics on a non-empty page, `0xFFFF` or more inodes, an empty key or (a branch) a child
id equal to the page's: excluded by the premises. -/
abbrev node.write.spec : Prop :=
  ∀ (n : Loc) (nv : node) (ins : List Inode) (ms : List InodeM) (dq dqi : DFrac)
    (qk qv : Nat → DFrac) (p : Loc)
    (hdr : Page) (R : Nat),
  hdr.count' = W16 0 → hdr.flags' = W16 0 → ms.length < 0xFFFF → pageFits ms →
  (pageBody true ms).length ≤ R → (nv.isLeaf' = false → ∀ m ∈ ms, m.pgid ≠ hdr.id') →
  0 < p.addr → p.addr + 16 + R ≤ maxAddr →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ n ↦{dq} nv ∗
      nv.inodes' ↦*{dqi} ins ∗
      ([∗list] k ↦ it;m ∈ ins;ms, ⌜it.flags' = m.flags ∧ it.pgid' = m.pgid⌝ ∗
        it.key' ↦*{qk k} m.key ∗ it.value' ↦*{qv k} m.value) ∗
      p ↦ hdr ∗ bytesPointsto (p +ₗ 16) (DFrac.own 1) (List.replicate R (W8 0)) }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"write")) (Val #p))
  {{ RET #(); n ↦{dq} nv ∗ nv.inodes' ↦*{dqi} ins ∗
      ([∗list] k ↦ it;m ∈ ins;ms, ⌜it.flags' = m.flags ∧ it.pgid' = m.pgid⌝ ∗
        it.key' ↦*{qk k} m.key ∗ it.value' ↦*{qv k} m.value) ∗
      p ↦ hdrWritten hdr nv.isLeaf' ms.length ∗
      bytesPointsto (p +ₗ 16) (DFrac.own 1)
        (pageBody nv.isLeaf' ms ++ List.replicate (R - (pageBody nv.isLeaf' ms).length) (W8 0)) }}

end spec

end bbolt
end EtcdGrove
end Perennial
