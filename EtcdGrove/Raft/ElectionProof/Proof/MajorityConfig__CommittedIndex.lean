/- Port of election_proof/proof_MajorityConfig__CommittedIndex.v.

Lean notes: the pure helper file `proof_MajorityConfig__CommittedIndex_helpers/
committed_index.v` (`fill_perm`, `sorted_quorum_index`) is not ported yet: the main
path it serves is blocked by the generated code (see the `sorry` below).
-/
import EtcdGrove.Raft.ElectionProof.Spec.MajorityConfig__CommittedIndex
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

/-- The two `len(c) == 0` exits (the nil component, and a real but empty map), then
the main path in four phases: the `if` choosing the stack buffer or a heap slice is
joined at "`srt` is `n` zeros"; the map range fills `srt` from the right (invariant:
after `k` voters, `srt` is `n - J` zeros followed by the `J` acknowledgements among
them, reversed, and `i = n - 1 - J`); `slices.Sort`; the read at `pos = n - (n/2+1)`.
`fill_perm` and `sorted_quorum_index` turn the sorted slice into `IsQuorumIndex`. -/
theorem quorum.MajorityConfig.CommittedIndex.wp_proof
    (wp_slices_Sort : slices.«Sort».spec (GF := GF) (hG := hG)) :
    quorum.MajorityConfig.CommittedIndex.spec (GF := GF) (hG := hG) := by
  intro cs cref mref l Pres acked
  wp_start as ⟨%Hsz, Hc, Hm, #Hl, HP⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  icases Hm with (⟨%Hnil, %Hs⟩ | ⟨%ids, %Hids, Hids⟩)
  · -- the nil component: `len(c) == 0`.
    -- NOT PROVABLE in the Lean semantics as it stands (as for `MajorityConfig.VoteResult`):
    -- Perennial's Lean `len_map` unfolds `len(m)` to `InternalMapLength (Read m)`, which
    -- reads the map pointer unconditionally, so `len` of `map.nil` is stuck; Rocq steps
    -- it with `pure_wp_map_nil_len`, which the Lean port of Perennial does not have
    -- (`wp_map_len`: "`len` of a nil map is not covered"). What is left: the `WP` of the
    -- body at `mref = map.nil`, `cs = ∅`; the rest is the `MaxUint64` exit as below.
    sorry
  wp_apply wp_map_len (t := quorum.MajorityConfig.ty) $$ Hids as Hids
  -- `wp_join` below would substitute `cs := domSet ids` anyway; do it now
  subst Hids
  by_cases Hemp : domSet ids = ∅
  · -- a real but empty map: `len(c) == 0` too
    have Hz : GMap.size ids = 0 := by
      rw [(GMap.dom_empty_iff_L ids).1 Hemp, GMap.map_size_empty]
    rw [Hz]
    wp_auto
    iapply HΦ
    iframe Hc HP
    isplitl [Hids]
    · iright
      iexists ids
      iframe Hids
      ipureintro; rfl
    ipureintro
    exact ⟨fun _ => rfl, fun h => absurd Hemp h⟩
  -- **Blocked by the generated code** (`Perennial/Code/go_etcd_io/raft/v3/quorum.lean`,
  -- `MajorityConfig.CommittedIndex.impl`, lines 547-549): the Lean translation still has
  -- the two Goose bugs the Rocq code at feb5c73d4 no longer has (see
  -- `Spec/ProgressTracker__Visit.lean`, "Two tooling obstacles"): `len(stk) >= n` is
  -- `GoOp GoGe go.int (FuncResolve go.len [ArrayType 7 uint64] #(), ![go.int] n)`, the
  -- *unapplied* function value compared as an `int` (no step reduces it, so the `if` is
  -- stuck), and `srt = stk[:n]` slices the loaded array *value*, where
  -- `slice_array_step` steps only on a location. The rest of the Rocq proof (`wp_if_join`
  -- at "`srt` is `n` zeros", the map range filling `srt` from the right, `slices.Sort`,
  -- the read at `pos`, `fill_perm` and `sorted_quorum_index`) cannot start until the
  -- Lean code is regenerated with the fixed Goose.
  sorry

end proof

end EtcdGrove
end Perennial
