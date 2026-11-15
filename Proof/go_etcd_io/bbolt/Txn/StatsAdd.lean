/-
`TxStats.add` over plain points-tos (U5 of `notes/bbolt-proof-plan.md`): `removeTx` and the
writer's `close` merge a closed transaction's statistics (persistent, `txDone`'s) into the
database's (`statlock`'s `Ps`). Each `Get*`/`Inc*` is an atomic access to one field of an owned
`TxStats`.
-/
module

public import Proof.go_etcd_io.bbolt.Txn.Stats

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section plain
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit hos in
/-- `atomicLoadDuration(ptr)` at any fraction. -/
theorem wp_atomicLoadDuration_dq (ptr : Loc) (dq : DFrac) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt -∗
    (|={⊤,∅}=> ▷ ∃ v : w64, ptr ↦{dq} v ∗ (ptr ↦{dq} v ={∅,⊤}=∗ Φ #v)) -∗
    WP (App (Val #(functions atomicLoadDuration [])) (Val #ptr)) {{ Φ }} := by
  wp_start as _
  wp_auto
  wp_apply_core sync.atomic.wp_LoadInt64 $$ [] [HΦ «$res0»]
  · iPkgInit
  imod HΦ with ⟨%v, Hp, HΦ⟩
  imodintro; inext
  iexists v
  iframe Hp
  iintro Hp
  imod HΦ $$ Hp with HΦ
  imodintro
  wp_auto
  iexact HΦ

omit hos in
theorem wp_TxStats_IncPageCount_plain (s : Loc) (v : TxStats) (d : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ s ↦ v }}
      (App (Val (s @!! go.GoType.PointerType TxStats.ty @!! go!"IncPageCount")) (Val #d))
    {{ (n : w64), RET #n; ∃ v' : TxStats, s ↦ v' }} := by
  wp_start as Hs
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  wp_apply_core sync.atomic.wp_AddInt64 $$ [] [Hs HΦ «$res0»]
  · iexact Hatomic
  icases (TxStats.TxStats_access_store_PageCount _ v (v.PageCount' + d)).access_strict $$ Hs
    with ⟨Hf, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists v.PageCount'
  iframe Hf
  iintro Hf
  imod Hmask with -
  ihave Hs := Hclose $$ Hf
  imodintro
  wp_auto
  iapply HΦ
  iexists _; iexact Hs

omit hos in
theorem wp_TxStats_GetPageCount_plain (o : Loc) (w : TxStats) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ o ↦{dq} w }}
      (App (Val (o @!! go.GoType.PointerType TxStats.ty @!! go!"GetPageCount")) (Val #()))
    {{ (n : w64), RET #n; o ↦{dq} w }} := by
  wp_start as Ho
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  wp_apply_core sync.atomic.wp_LoadInt64 $$ [] [Ho HΦ «$res0»]
  · iexact Hatomic
  icases (TxStats.TxStats_access_load_PageCount _ w dq).access_strict $$ Ho with ⟨Hf, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists w.PageCount'
  iframe Hf
  iintro Hf
  imod Hmask with -
  ihave Ho := Hclose $$ Hf
  imodintro
  wp_auto
  iapply HΦ $$ Ho

omit hos in
theorem wp_TxStats_IncPageAlloc_plain (s : Loc) (v : TxStats) (d : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ s ↦ v }}
      (App (Val (s @!! go.GoType.PointerType TxStats.ty @!! go!"IncPageAlloc")) (Val #d))
    {{ (n : w64), RET #n; ∃ v' : TxStats, s ↦ v' }} := by
  wp_start as Hs
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  wp_apply_core sync.atomic.wp_AddInt64 $$ [] [Hs HΦ «$res0»]
  · iexact Hatomic
  icases (TxStats.TxStats_access_store_PageAlloc _ v (v.PageAlloc' + d)).access_strict $$ Hs
    with ⟨Hf, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists v.PageAlloc'
  iframe Hf
  iintro Hf
  imod Hmask with -
  ihave Hs := Hclose $$ Hf
  imodintro
  wp_auto
  iapply HΦ
  iexists _; iexact Hs

omit hos in
theorem wp_TxStats_GetPageAlloc_plain (o : Loc) (w : TxStats) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ o ↦{dq} w }}
      (App (Val (o @!! go.GoType.PointerType TxStats.ty @!! go!"GetPageAlloc")) (Val #()))
    {{ (n : w64), RET #n; o ↦{dq} w }} := by
  wp_start as Ho
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  wp_apply_core sync.atomic.wp_LoadInt64 $$ [] [Ho HΦ «$res0»]
  · iexact Hatomic
  icases (TxStats.TxStats_access_load_PageAlloc _ w dq).access_strict $$ Ho with ⟨Hf, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists w.PageAlloc'
  iframe Hf
  iintro Hf
  imod Hmask with -
  ihave Ho := Hclose $$ Hf
  imodintro
  wp_auto
  iapply HΦ $$ Ho

omit hos in
theorem wp_TxStats_IncCursorCount_plain (s : Loc) (v : TxStats) (d : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ s ↦ v }}
      (App (Val (s @!! go.GoType.PointerType TxStats.ty @!! go!"IncCursorCount")) (Val #d))
    {{ (n : w64), RET #n; ∃ v' : TxStats, s ↦ v' }} := by
  wp_start as Hs
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  wp_apply_core sync.atomic.wp_AddInt64 $$ [] [Hs HΦ «$res0»]
  · iexact Hatomic
  icases (TxStats.TxStats_access_store_CursorCount _ v (v.CursorCount' + d)).access_strict $$ Hs
    with ⟨Hf, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists v.CursorCount'
  iframe Hf
  iintro Hf
  imod Hmask with -
  ihave Hs := Hclose $$ Hf
  imodintro
  wp_auto
  iapply HΦ
  iexists _; iexact Hs

omit hos in
theorem wp_TxStats_GetCursorCount_plain (o : Loc) (w : TxStats) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ o ↦{dq} w }}
      (App (Val (o @!! go.GoType.PointerType TxStats.ty @!! go!"GetCursorCount")) (Val #()))
    {{ (n : w64), RET #n; o ↦{dq} w }} := by
  wp_start as Ho
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  wp_apply_core sync.atomic.wp_LoadInt64 $$ [] [Ho HΦ «$res0»]
  · iexact Hatomic
  icases (TxStats.TxStats_access_load_CursorCount _ w dq).access_strict $$ Ho with ⟨Hf, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists w.CursorCount'
  iframe Hf
  iintro Hf
  imod Hmask with -
  ihave Ho := Hclose $$ Hf
  imodintro
  wp_auto
  iapply HΦ $$ Ho

omit hos in
theorem wp_TxStats_IncNodeCount_plain (s : Loc) (v : TxStats) (d : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ s ↦ v }}
      (App (Val (s @!! go.GoType.PointerType TxStats.ty @!! go!"IncNodeCount")) (Val #d))
    {{ (n : w64), RET #n; ∃ v' : TxStats, s ↦ v' }} := by
  wp_start as Hs
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  wp_apply_core sync.atomic.wp_AddInt64 $$ [] [Hs HΦ «$res0»]
  · iexact Hatomic
  icases (TxStats.TxStats_access_store_NodeCount _ v (v.NodeCount' + d)).access_strict $$ Hs
    with ⟨Hf, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists v.NodeCount'
  iframe Hf
  iintro Hf
  imod Hmask with -
  ihave Hs := Hclose $$ Hf
  imodintro
  wp_auto
  iapply HΦ
  iexists _; iexact Hs

omit hos in
theorem wp_TxStats_GetNodeCount_plain (o : Loc) (w : TxStats) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ o ↦{dq} w }}
      (App (Val (o @!! go.GoType.PointerType TxStats.ty @!! go!"GetNodeCount")) (Val #()))
    {{ (n : w64), RET #n; o ↦{dq} w }} := by
  wp_start as Ho
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  wp_apply_core sync.atomic.wp_LoadInt64 $$ [] [Ho HΦ «$res0»]
  · iexact Hatomic
  icases (TxStats.TxStats_access_load_NodeCount _ w dq).access_strict $$ Ho with ⟨Hf, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists w.NodeCount'
  iframe Hf
  iintro Hf
  imod Hmask with -
  ihave Ho := Hclose $$ Hf
  imodintro
  wp_auto
  iapply HΦ $$ Ho

omit hos in
theorem wp_TxStats_IncNodeDeref_plain (s : Loc) (v : TxStats) (d : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ s ↦ v }}
      (App (Val (s @!! go.GoType.PointerType TxStats.ty @!! go!"IncNodeDeref")) (Val #d))
    {{ (n : w64), RET #n; ∃ v' : TxStats, s ↦ v' }} := by
  wp_start as Hs
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  wp_apply_core sync.atomic.wp_AddInt64 $$ [] [Hs HΦ «$res0»]
  · iexact Hatomic
  icases (TxStats.TxStats_access_store_NodeDeref _ v (v.NodeDeref' + d)).access_strict $$ Hs
    with ⟨Hf, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists v.NodeDeref'
  iframe Hf
  iintro Hf
  imod Hmask with -
  ihave Hs := Hclose $$ Hf
  imodintro
  wp_auto
  iapply HΦ
  iexists _; iexact Hs

omit hos in
theorem wp_TxStats_GetNodeDeref_plain (o : Loc) (w : TxStats) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ o ↦{dq} w }}
      (App (Val (o @!! go.GoType.PointerType TxStats.ty @!! go!"GetNodeDeref")) (Val #()))
    {{ (n : w64), RET #n; o ↦{dq} w }} := by
  wp_start as Ho
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  wp_apply_core sync.atomic.wp_LoadInt64 $$ [] [Ho HΦ «$res0»]
  · iexact Hatomic
  icases (TxStats.TxStats_access_load_NodeDeref _ w dq).access_strict $$ Ho with ⟨Hf, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists w.NodeDeref'
  iframe Hf
  iintro Hf
  imod Hmask with -
  ihave Ho := Hclose $$ Hf
  imodintro
  wp_auto
  iapply HΦ $$ Ho

omit hos in
theorem wp_TxStats_IncRebalance_plain (s : Loc) (v : TxStats) (d : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ s ↦ v }}
      (App (Val (s @!! go.GoType.PointerType TxStats.ty @!! go!"IncRebalance")) (Val #d))
    {{ (n : w64), RET #n; ∃ v' : TxStats, s ↦ v' }} := by
  wp_start as Hs
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  wp_apply_core sync.atomic.wp_AddInt64 $$ [] [Hs HΦ «$res0»]
  · iexact Hatomic
  icases (TxStats.TxStats_access_store_Rebalance _ v (v.Rebalance' + d)).access_strict $$ Hs
    with ⟨Hf, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists v.Rebalance'
  iframe Hf
  iintro Hf
  imod Hmask with -
  ihave Hs := Hclose $$ Hf
  imodintro
  wp_auto
  iapply HΦ
  iexists _; iexact Hs

omit hos in
theorem wp_TxStats_GetRebalance_plain (o : Loc) (w : TxStats) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ o ↦{dq} w }}
      (App (Val (o @!! go.GoType.PointerType TxStats.ty @!! go!"GetRebalance")) (Val #()))
    {{ (n : w64), RET #n; o ↦{dq} w }} := by
  wp_start as Ho
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  wp_apply_core sync.atomic.wp_LoadInt64 $$ [] [Ho HΦ «$res0»]
  · iexact Hatomic
  icases (TxStats.TxStats_access_load_Rebalance _ w dq).access_strict $$ Ho with ⟨Hf, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists w.Rebalance'
  iframe Hf
  iintro Hf
  imod Hmask with -
  ihave Ho := Hclose $$ Hf
  imodintro
  wp_auto
  iapply HΦ $$ Ho

theorem wp_TxStats_IncRebalanceTime_plain (s : Loc) (v : TxStats) (d : time.Duration) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ s ↦ v }}
      (App (Val (s @!! go.GoType.PointerType TxStats.ty @!! go!"IncRebalanceTime")) (Val #d))
    {{ (n : time.Duration), RET #n; ∃ v' : TxStats, s ↦ v' }} := by
  wp_start as Hs
  wp_auto
  wp_apply_core wp_atomicAddDuration $$ [] [Hs HΦ «$res0»]
  · iexact Hpkg
  icases (TxStats.TxStats_access_store_RebalanceTime _ v (v.RebalanceTime' + d)).access_strict $$ Hs
    with ⟨Hf, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists v.RebalanceTime'
  iframe Hf
  iintro Hf
  imod Hmask with -
  ihave Hs := Hclose $$ Hf
  imodintro
  wp_auto
  iapply HΦ
  iexists _; iexact Hs

omit hos in
theorem wp_TxStats_GetRebalanceTime_plain (o : Loc) (w : TxStats) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ o ↦{dq} w }}
      (App (Val (o @!! go.GoType.PointerType TxStats.ty @!! go!"GetRebalanceTime")) (Val #()))
    {{ (n : time.Duration), RET #n; o ↦{dq} w }} := by
  wp_start as Ho
  wp_auto
  wp_apply_core wp_atomicLoadDuration_dq $$ [] [Ho HΦ «$res0»]
  · iexact Hpkg
  icases (TxStats.TxStats_access_load_RebalanceTime _ w dq).access_strict $$ Ho with ⟨Hf, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists w.RebalanceTime'
  iframe Hf
  iintro Hf
  imod Hmask with -
  ihave Ho := Hclose $$ Hf
  imodintro
  wp_auto
  iapply HΦ $$ Ho

omit hos in
theorem wp_TxStats_IncSplit_plain (s : Loc) (v : TxStats) (d : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ s ↦ v }}
      (App (Val (s @!! go.GoType.PointerType TxStats.ty @!! go!"IncSplit")) (Val #d))
    {{ (n : w64), RET #n; ∃ v' : TxStats, s ↦ v' }} := by
  wp_start as Hs
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  wp_apply_core sync.atomic.wp_AddInt64 $$ [] [Hs HΦ «$res0»]
  · iexact Hatomic
  icases (TxStats.TxStats_access_store_Split _ v (v.Split' + d)).access_strict $$ Hs
    with ⟨Hf, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists v.Split'
  iframe Hf
  iintro Hf
  imod Hmask with -
  ihave Hs := Hclose $$ Hf
  imodintro
  wp_auto
  iapply HΦ
  iexists _; iexact Hs

omit hos in
theorem wp_TxStats_GetSplit_plain (o : Loc) (w : TxStats) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ o ↦{dq} w }}
      (App (Val (o @!! go.GoType.PointerType TxStats.ty @!! go!"GetSplit")) (Val #()))
    {{ (n : w64), RET #n; o ↦{dq} w }} := by
  wp_start as Ho
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  wp_apply_core sync.atomic.wp_LoadInt64 $$ [] [Ho HΦ «$res0»]
  · iexact Hatomic
  icases (TxStats.TxStats_access_load_Split _ w dq).access_strict $$ Ho with ⟨Hf, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists w.Split'
  iframe Hf
  iintro Hf
  imod Hmask with -
  ihave Ho := Hclose $$ Hf
  imodintro
  wp_auto
  iapply HΦ $$ Ho

omit hos in
theorem wp_TxStats_IncSpill_plain (s : Loc) (v : TxStats) (d : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ s ↦ v }}
      (App (Val (s @!! go.GoType.PointerType TxStats.ty @!! go!"IncSpill")) (Val #d))
    {{ (n : w64), RET #n; ∃ v' : TxStats, s ↦ v' }} := by
  wp_start as Hs
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  wp_apply_core sync.atomic.wp_AddInt64 $$ [] [Hs HΦ «$res0»]
  · iexact Hatomic
  icases (TxStats.TxStats_access_store_Spill _ v (v.Spill' + d)).access_strict $$ Hs
    with ⟨Hf, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists v.Spill'
  iframe Hf
  iintro Hf
  imod Hmask with -
  ihave Hs := Hclose $$ Hf
  imodintro
  wp_auto
  iapply HΦ
  iexists _; iexact Hs

omit hos in
theorem wp_TxStats_GetSpill_plain (o : Loc) (w : TxStats) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ o ↦{dq} w }}
      (App (Val (o @!! go.GoType.PointerType TxStats.ty @!! go!"GetSpill")) (Val #()))
    {{ (n : w64), RET #n; o ↦{dq} w }} := by
  wp_start as Ho
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  wp_apply_core sync.atomic.wp_LoadInt64 $$ [] [Ho HΦ «$res0»]
  · iexact Hatomic
  icases (TxStats.TxStats_access_load_Spill _ w dq).access_strict $$ Ho with ⟨Hf, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists w.Spill'
  iframe Hf
  iintro Hf
  imod Hmask with -
  ihave Ho := Hclose $$ Hf
  imodintro
  wp_auto
  iapply HΦ $$ Ho

theorem wp_TxStats_IncSpillTime_plain (s : Loc) (v : TxStats) (d : time.Duration) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ s ↦ v }}
      (App (Val (s @!! go.GoType.PointerType TxStats.ty @!! go!"IncSpillTime")) (Val #d))
    {{ (n : time.Duration), RET #n; ∃ v' : TxStats, s ↦ v' }} := by
  wp_start as Hs
  wp_auto
  wp_apply_core wp_atomicAddDuration $$ [] [Hs HΦ «$res0»]
  · iexact Hpkg
  icases (TxStats.TxStats_access_store_SpillTime _ v (v.SpillTime' + d)).access_strict $$ Hs
    with ⟨Hf, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists v.SpillTime'
  iframe Hf
  iintro Hf
  imod Hmask with -
  ihave Hs := Hclose $$ Hf
  imodintro
  wp_auto
  iapply HΦ
  iexists _; iexact Hs

omit hos in
theorem wp_TxStats_GetSpillTime_plain (o : Loc) (w : TxStats) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ o ↦{dq} w }}
      (App (Val (o @!! go.GoType.PointerType TxStats.ty @!! go!"GetSpillTime")) (Val #()))
    {{ (n : time.Duration), RET #n; o ↦{dq} w }} := by
  wp_start as Ho
  wp_auto
  wp_apply_core wp_atomicLoadDuration_dq $$ [] [Ho HΦ «$res0»]
  · iexact Hpkg
  icases (TxStats.TxStats_access_load_SpillTime _ w dq).access_strict $$ Ho with ⟨Hf, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists w.SpillTime'
  iframe Hf
  iintro Hf
  imod Hmask with -
  ihave Ho := Hclose $$ Hf
  imodintro
  wp_auto
  iapply HΦ $$ Ho

omit hos in
theorem wp_TxStats_IncWrite_plain (s : Loc) (v : TxStats) (d : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ s ↦ v }}
      (App (Val (s @!! go.GoType.PointerType TxStats.ty @!! go!"IncWrite")) (Val #d))
    {{ (n : w64), RET #n; ∃ v' : TxStats, s ↦ v' }} := by
  wp_start as Hs
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  wp_apply_core sync.atomic.wp_AddInt64 $$ [] [Hs HΦ «$res0»]
  · iexact Hatomic
  icases (TxStats.TxStats_access_store_Write _ v (v.Write' + d)).access_strict $$ Hs
    with ⟨Hf, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists v.Write'
  iframe Hf
  iintro Hf
  imod Hmask with -
  ihave Hs := Hclose $$ Hf
  imodintro
  wp_auto
  iapply HΦ
  iexists _; iexact Hs

omit hos in
theorem wp_TxStats_GetWrite_plain (o : Loc) (w : TxStats) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ o ↦{dq} w }}
      (App (Val (o @!! go.GoType.PointerType TxStats.ty @!! go!"GetWrite")) (Val #()))
    {{ (n : w64), RET #n; o ↦{dq} w }} := by
  wp_start as Ho
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  wp_apply_core sync.atomic.wp_LoadInt64 $$ [] [Ho HΦ «$res0»]
  · iexact Hatomic
  icases (TxStats.TxStats_access_load_Write _ w dq).access_strict $$ Ho with ⟨Hf, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists w.Write'
  iframe Hf
  iintro Hf
  imod Hmask with -
  ihave Ho := Hclose $$ Hf
  imodintro
  wp_auto
  iapply HΦ $$ Ho

theorem wp_TxStats_IncWriteTime_plain (s : Loc) (v : TxStats) (d : time.Duration) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ s ↦ v }}
      (App (Val (s @!! go.GoType.PointerType TxStats.ty @!! go!"IncWriteTime")) (Val #d))
    {{ (n : time.Duration), RET #n; ∃ v' : TxStats, s ↦ v' }} := by
  wp_start as Hs
  wp_auto
  wp_apply_core wp_atomicAddDuration $$ [] [Hs HΦ «$res0»]
  · iexact Hpkg
  icases (TxStats.TxStats_access_store_WriteTime _ v (v.WriteTime' + d)).access_strict $$ Hs
    with ⟨Hf, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists v.WriteTime'
  iframe Hf
  iintro Hf
  imod Hmask with -
  ihave Hs := Hclose $$ Hf
  imodintro
  wp_auto
  iapply HΦ
  iexists _; iexact Hs

omit hos in
theorem wp_TxStats_GetWriteTime_plain (o : Loc) (w : TxStats) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ o ↦{dq} w }}
      (App (Val (o @!! go.GoType.PointerType TxStats.ty @!! go!"GetWriteTime")) (Val #()))
    {{ (n : time.Duration), RET #n; o ↦{dq} w }} := by
  wp_start as Ho
  wp_auto
  wp_apply_core wp_atomicLoadDuration_dq $$ [] [Ho HΦ «$res0»]
  · iexact Hpkg
  icases (TxStats.TxStats_access_load_WriteTime _ w dq).access_strict $$ Ho with ⟨Hf, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists w.WriteTime'
  iframe Hf
  iintro Hf
  imod Hmask with -
  ihave Ho := Hclose $$ Hf
  imodintro
  wp_auto
  iapply HΦ $$ Ho

/-- **`s.add(other)`**: the database's statistics `s` (owned) plus a transaction's `other` (any
fraction). -/
theorem wp_TxStats_add (s o : Loc) (v w : TxStats) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ s ↦ v ∗ o ↦{dq} w }}
      (App (Val (s @!! go.GoType.PointerType TxStats.ty @!! go!"add")) (Val #o))
    {{ RET #(); (∃ v' : TxStats, s ↦ v') ∗ o ↦{dq} w }} := by
  wp_start as ⟨Hs, Ho⟩
  wp_auto
  wp_apply wp_TxStats_GetPageCount_plain o w dq $$ [Ho] as %n0 Ho
  · iframe
  wp_apply wp_TxStats_IncPageCount_plain s _ n0 $$ [Hs] as %m0 ⟨%v0, Hs⟩
  · iframe
  wp_apply wp_TxStats_GetPageAlloc_plain o w dq $$ [Ho] as %n1 Ho
  · iframe
  wp_apply wp_TxStats_IncPageAlloc_plain s _ n1 $$ [Hs] as %m1 ⟨%v1, Hs⟩
  · iframe
  wp_apply wp_TxStats_GetCursorCount_plain o w dq $$ [Ho] as %n2 Ho
  · iframe
  wp_apply wp_TxStats_IncCursorCount_plain s _ n2 $$ [Hs] as %m2 ⟨%v2, Hs⟩
  · iframe
  wp_apply wp_TxStats_GetNodeCount_plain o w dq $$ [Ho] as %n3 Ho
  · iframe
  wp_apply wp_TxStats_IncNodeCount_plain s _ n3 $$ [Hs] as %m3 ⟨%v3, Hs⟩
  · iframe
  wp_apply wp_TxStats_GetNodeDeref_plain o w dq $$ [Ho] as %n4 Ho
  · iframe
  wp_apply wp_TxStats_IncNodeDeref_plain s _ n4 $$ [Hs] as %m4 ⟨%v4, Hs⟩
  · iframe
  wp_apply wp_TxStats_GetRebalance_plain o w dq $$ [Ho] as %n5 Ho
  · iframe
  wp_apply wp_TxStats_IncRebalance_plain s _ n5 $$ [Hs] as %m5 ⟨%v5, Hs⟩
  · iframe
  wp_apply wp_TxStats_GetRebalanceTime_plain o w dq $$ [Ho] as %n6 Ho
  · iframe
  wp_apply wp_TxStats_IncRebalanceTime_plain s _ n6 $$ [Hs] as %m6 ⟨%v6, Hs⟩
  · iframe
  wp_apply wp_TxStats_GetSplit_plain o w dq $$ [Ho] as %n7 Ho
  · iframe
  wp_apply wp_TxStats_IncSplit_plain s _ n7 $$ [Hs] as %m7 ⟨%v7, Hs⟩
  · iframe
  wp_apply wp_TxStats_GetSpill_plain o w dq $$ [Ho] as %n8 Ho
  · iframe
  wp_apply wp_TxStats_IncSpill_plain s _ n8 $$ [Hs] as %m8 ⟨%v8, Hs⟩
  · iframe
  wp_apply wp_TxStats_GetSpillTime_plain o w dq $$ [Ho] as %n9 Ho
  · iframe
  wp_apply wp_TxStats_IncSpillTime_plain s _ n9 $$ [Hs] as %m9 ⟨%v9, Hs⟩
  · iframe
  wp_apply wp_TxStats_GetWrite_plain o w dq $$ [Ho] as %n10 Ho
  · iframe
  wp_apply wp_TxStats_IncWrite_plain s _ n10 $$ [Hs] as %m10 ⟨%v10, Hs⟩
  · iframe
  wp_apply wp_TxStats_GetWriteTime_plain o w dq $$ [Ho] as %n11 Ho
  · iframe
  wp_apply wp_TxStats_IncWriteTime_plain s _ n11 $$ [Hs] as %m11 ⟨%v11, Hs⟩
  · iframe
  iapply HΦ
  iframe Ho
  iexists _; iexact Hs

end plain

end bbolt
end EtcdGrove
end Perennial
