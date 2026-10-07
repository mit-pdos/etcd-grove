/- Port of election_proof/proof_ProgressTracker__Visit.v.

Lean notes: Rocq's `wp_if_join` is `wp_join`.
-/
import EtcdGrove.Raft.ElectionProof.Spec.ProgressTracker__Visit
import EtcdGrove.Raft.ElectionProof.Spec.slices_Sort

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem tracker.ProgressTracker.Visit.wp_proof
    (wp_slices_Sort : slices.«Sort».spec (GF := GF) (hG := hG)) :
    tracker.ProgressTracker.Visit.spec (GF := GF) (hG := hG) := by
  intro cfg trk tv t f I
  obtain ⟨votes, prs, pvs⟩ := t
  dsimp only
  wp_start as ⟨Htrk, Hown, HI, #Hf⟩
  iNamed Hown
  wp_auto
  -- `n := len(p.Progress)`
  wp_apply wp_ProgressMap_len $$ Hprs as -
  -- **Blocked by the generated code** (`Perennial/Code/go_etcd_io/raft/v3/tracker.lean`,
  -- `ProgressTracker.Visit.impl`, lines 1067-1069). The Lean translation still has the
  -- two Goose bugs that the Rocq code at feb5c73d4 no longer has (see the spec's
  -- comment, "Two tooling obstacles", fixed in Goose 2026-09-17):
  -- 1. `len(sl) >= n` is emitted as
  --    `GoOp GoGe go.int (FuncResolve go.len [ArrayType 7 uint64] #(), ![go.int] n)`:
  --    the *unapplied* function value `#(functions go.len [..])` compared as an `int`.
  --    No step reduces it (`wp_auto` parks right here), so the `if` is stuck;
  -- 2. `ids = sl[:n]` is `Slice (ArrayType 7 uint64) (![ArrayType 7 uint64] sl, 0, n)`,
  --    a slice of the loaded array *value*, where `slice_array_step` steps only on an
  --    array location.
  -- The Rocq proof goes on with `wp_if_join` at "`ids` is a slice of `n` slots"
  -- (`slice_array` + `ownSlice_split_all` / `wp_slice_make2`), the map range filling
  -- `ids` backwards (`wp_map_for_range`), `slices.Sort`, and the slice range applying
  -- `visitClosure` with `ownTracker_lookup`. None of it can start until the Lean code
  -- is regenerated with the fixed Goose.
  sorry

end proof

end EtcdGrove
end Perennial
