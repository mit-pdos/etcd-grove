/-
Port of election_proof/spec_slices_Sort.v (feb5c73d4).

Lean notes:
* Go's `slices.Sort` is `Perennial.slices.«Sort»` in the generated code (`Sort` is a
  Lean keyword); the type arguments `[go.SliceType go.uint64; go.uint64]` are
  `[go.GoType.SliceType go.uint64, go.uint64]`.
* Rocq's `xs' !! i` (`i : nat`) is `xs'[i]?`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `slices.Sort` on a `[]uint64`: the slice is permuted **and sorted ascending**.
`Perennial.Proof.slices_proof.sort` proves it (`slices.wp_Sort_uint64`), and
`Proof/slices_Sort.lean` is that theorem.

The length bound is Perennial's: past `2^62` elements, the heapsort fallback's
`2*root+1` overflows `int`, so the call can panic. The callers sort voter ids, and
the configuration carries the bound (`ownTracker`'s `Hcfg_size`).

`campaign`, `Visit`, `VoterNodes` and `MajorityConfig.Slice` need only the
permutation. `MajorityConfig.CommittedIndex` needs the order: it reads the quorum
index off the sorted acknowledgements at a fixed position. -/
abbrev slices.«Sort».spec : Prop :=
  ∀ (data : GoSlice) (xs : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗ data ↦* xs ∗ ⌜xs.length ≤ 2 ^ 62⌝ }}
    (App (Val #(functions _root_.Perennial.slices.«Sort»
        [go.GoType.SliceType go.uint64, go.uint64])) (Val #data))
  {{ (xs' : List w64), RET #();
      data ↦* xs' ∗ ⌜xs ≡ₚ xs'⌝ ∗
      ⌜∀ (i j : Nat) (xi xj : w64), xs'[i]? = some xi → xs'[j]? = some xj →
          i < j → uint.Z xi ≤ uint.Z xj⌝ }}

end spec

end EtcdGrove
end Perennial
