/-
The proof of `hashStorage.Store` (`hash.go`; sortslice, 2026-11-24, until then a trust-boundary
axiom): it logs, takes `hashMu` (its guard is in `hashStorageOk`, over `hashesR`), appends the hash,
sorts the hashes by revision with `slices.SortFunc` (the fork's a336e97f9; until then
`sort.Slice`, which Perennial does not model) over `cmp.Compare`, keeps the last
`hashStorageMaxSize` and unlocks.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.hashStorage__Store
public import Spec.go_uber_org.zap.Uint32
public import Spec.go_uber_org.zap.Int64
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.cmp.Compare
public import Perennial.Proof.slices.Link
public import Perennial.Proof.sync.Results

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The order `Store` sorts by: a hash's revision, signed. -/
def mvcc.hashRevLt (a b : KeyValueHash) : Prop := sint.Z a.Revision' < sint.Z b.Revision'

theorem mvcc.hashRevLt_swo : _root_.Perennial.slices.StrictWeakOrder mvcc.hashRevLt where
  strict_weak_order_irrefl _ := by unfold mvcc.hashRevLt; omega
  strict_weak_order_trans _ _ _ h1 h2 := by unfold mvcc.hashRevLt at *; omega
  strict_weak_order_equiv :=
    ⟨fun _ => by unfold mvcc.hashRevLt; omega,
     fun h => by unfold mvcc.hashRevLt at *; omega,
     fun h1 h2 => by unfold mvcc.hashRevLt at *; omega⟩

theorem mvcc.hashStorage.Store.wp_proof
    (hUint32 : zap.Uint32.spec (GF := GF) (hG := hG))
    (hInt64 : zap.Int64.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hCompare : cmp.Compare.spec (GF := GF) (hG := hG)) :
    mvcc.hashStorage.Store.spec (GF := GF) (hG := hG) := by
  intro hp h
  wp_start as #Hok
  iunfold mvcc.hashStorageOk at Hok
  icases Hok with ⟨%lg, #Hlg, #Hzap, #Hg⟩
  wp_apply wp_with_defer as %defer defer
  wp_apply hUint32 as %f1 -
  (try wp_auto)
  wp_apply hInt64 as %f2 -
  (try wp_auto)
  wp_apply hInt64 as %f3 -
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %fs ⟨Hfs, -⟩
  (try wp_auto)
  wp_apply (hInfo lg) $$ []
  · iframe #
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Lock_guard $$ [$Hg] as ⟨Hlk, HP⟩
  iunfold mvcc.hashesR at HP
  icases HP with ⟨%sl, %xs, Hf, Hsl, Hcap, %Hlen⟩
  (try wp_auto)
  wp_apply wp_slice_literal (V := KeyValueHash) [h]
  isplitr
  · ipureintro; rfl
  iintro %sl2 ⟨Hsl2, -⟩
  (try wp_auto)
  wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl2] as %s1 ⟨Hsl, Hcap, -⟩
  (try wp_auto)
  wp_func_lits
  (try wp_auto)
  wp_apply (_root_.Perennial.slices.wp_SortFunc mvcc.hashRevLt s1 _ (xs ++ [h]) mvcc.hashRevLt_swo)
    $$ [$Hsl] as %ys ⟨Hsl, %Hperm, -⟩
  · isplitr
    · ipureintro; simp only [List.length_append, List.length_singleton]; omega
    unfold _root_.Perennial.slices.cmpImplements
    iintro %a %b
    iintro !> %Φ' _ HΦ'
    sorry
  (try wp_auto)
  sorry

end proof

end EtcdGrove
end Perennial
