/-
The `array` freelist meets the freelist interface's contracts: `FLImpl.Contract` (the methods
`shared` calls back) and `FLImpl.IfaceContract` (those its users call), from the specs of
`array`'s and `shared`'s methods (`*array`'s promoted methods load its `shared` and call
`shared`'s).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Iface
public import Proof.go_etcd_io.bbolt.internal.freelist.ArrayLemmas
public import Spec.go_etcd_io.bbolt.internal.freelist.array__FreeCount
public import Spec.go_etcd_io.bbolt.internal.freelist.array__freePageIds
public import Spec.go_etcd_io.bbolt.internal.freelist.array__Init
public import Spec.go_etcd_io.bbolt.internal.freelist.array__mergeSpans
public import Spec.go_etcd_io.bbolt.internal.freelist.array__Allocate
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__AddReadonlyTXID
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__RemoveReadonlyTXID
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__ReleasePendingPages
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__Free
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__Rollback
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__Freed
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__PendingCount
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__Count
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__Reload
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__NoSyncReload
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__EstimatedWritePageSize
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__Write

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

theorem arrayImpl.ity (a : Loc) : (arrayImpl (GF := GF) a).ity = go.GoType.PointerType array'.ty := rfl
theorem arrayImpl.iv (a : Loc) : (arrayImpl (GF := GF) a).iv = #a := rfl

/-! The methods `shared` calls back. -/

theorem arrayImpl.freeCountSpec (h : array.FreeCount.spec (GF := GF) (hG := hG)) (a : Loc) :
    (arrayImpl (GF := GF) a).FreeCountSpec := fun s free => h a s free

theorem arrayImpl.freePageIdsSpec (h : array.freePageIds.spec (GF := GF) (hG := hG)) (a : Loc) :
    (arrayImpl (GF := GF) a).FreePageIdsSpec := fun s free => h a s free

theorem arrayImpl.initSpec (h : array.Init.spec (GF := GF) (hG := hG)) (a : Loc) :
    (arrayImpl (GF := GF) a).InitSpec := fun s σ ids xs Hwf => h a s σ ids xs Hwf

theorem arrayImpl.mergeSpansSpec (h : array.mergeSpans.spec (GF := GF) (hG := hG)) (a : Loc) :
    (arrayImpl (GF := GF) a).MergeSpansSpec :=
  fun s free ids ys h1 h2 h3 => h a s free ids ys h1 h2 h3

theorem arrayImpl.contract (hFC : array.FreeCount.spec (GF := GF) (hG := hG))
    (hFPI : array.freePageIds.spec (GF := GF) (hG := hG))
    (hI : array.Init.spec (GF := GF) (hG := hG))
    (hM : array.mergeSpans.spec (GF := GF) (hG := hG)) (a : Loc) :
    (arrayImpl (GF := GF) a).Contract :=
  ⟨arrayImpl.freeCountSpec hFC a, arrayImpl.freePageIdsSpec hFPI a, arrayImpl.initSpec hI a,
    arrayImpl.mergeSpansSpec hM a⟩

/-! The methods the freelist's users call. -/

theorem arrayImpl.addReadonly (h : shared.AddReadonlyTXID.spec (GF := GF) (hG := hG)) (a : Loc) :
    (arrayImpl (GF := GF) a).AddReadonlySpec := by
  intro s σ tid
  rw [arrayImpl.ity, arrayImpl.iv]
  wp_start as Hfl
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  ihave #Hh : arrayHdl (GF := GF) a s $$ [Hhdl]
  · iExactEq Hhdl; rfl
  iunfold arrayHdl at Hh
  wp_auto
  wp_apply (h s _ σ tid) $$ [Hsh] as Hsh
  · iframe
  iapply HΦ
  unfold ownFL
  iframe
  iexact Hhdl

theorem arrayImpl.allocate (h : array.Allocate.spec (GF := GF) (hG := hG)) (a : Loc) :
    (arrayImpl (GF := GF) a).AllocateSpec := by
  intro s σ txid n Hn
  rw [arrayImpl.ity, arrayImpl.iv]
  iintro %Φ ⟨#Hpkg, Hfl⟩ HΦ
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  icases ownShared_wf _ _ _ $$ Hsh with ⟨Hsh, %Hwf⟩
  iapply (h a s σ txid n Hn) $$ [Hsh Hown]
  · unfold ownFL; iframe
    isplitl []
    · iexact Hpkg
    iexact Hhdl
  inext
  iintro %r Hr
  have Hn1 : 1 ≤ sint.nat n := by word
  icases Hr with (⟨%H0, Hfl⟩ | ⟨%i, %Hi, Hfl⟩)
  · iapply HΦ; ileft; iframe; ipureintro; exact H0.1
  · obtain ⟨Hrun, -, Hstart⟩ := Hi
    obtain ⟨Hb, Hmem, -⟩ := run_remove Hn1 Hwf.2.2.1 Hrun Hstart
    iapply HΦ; iright; iframe; ipureintro; exact ⟨Hb, Hmem⟩

theorem arrayImpl.removeReadonly (h : shared.RemoveReadonlyTXID.spec (GF := GF) (hG := hG)) (a : Loc) :
    (arrayImpl (GF := GF) a).RemoveReadonlySpec := by
  intro s σ tid
  rw [arrayImpl.ity, arrayImpl.iv]
  wp_start as Hfl
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  ihave #Hh : arrayHdl (GF := GF) a s $$ [Hhdl]
  · iExactEq Hhdl; rfl
  iunfold arrayHdl at Hh
  wp_auto
  wp_apply (h s _ σ tid) $$ [Hsh] as %ro ⟨%Hro, Hsh⟩
  · iframe
  iapply HΦ
  unfold ownFL
  iframe Hhdl
  iframe
  try (iExactEq Hown; rfl)
  ipureintro; exact Hro

theorem arrayImpl.free (h : shared.Free.spec (GF := GF) (hG := hG)) (a : Loc) :
    (arrayImpl (GF := GF) a).FreeSpec := by
  intro s σ txid p pv dq Hcan
  rw [arrayImpl.ity, arrayImpl.iv]
  wp_start as ⟨Hfl, Hp⟩
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  ihave #Hh : arrayHdl (GF := GF) a s $$ [Hhdl]
  · iExactEq Hhdl; rfl
  iunfold arrayHdl at Hh
  wp_auto
  wp_apply (h s _ σ txid p pv dq Hcan) $$ [Hsh Hp] as ⟨Hsh, Hp⟩
  · iframe
  iapply HΦ
  unfold ownFL
  iframe Hhdl
  iframe
  try (iExactEq Hown; rfl)

theorem arrayImpl.rollback (h : shared.Rollback.spec (GF := GF) (hG := hG)) (a : Loc) :
    (arrayImpl (GF := GF) a).RollbackSpec := by
  intro s σ txid Hcan
  rw [arrayImpl.ity, arrayImpl.iv]
  wp_start as Hfl
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  ihave #Hh : arrayHdl (GF := GF) a s $$ [Hhdl]
  · iExactEq Hhdl; rfl
  iunfold arrayHdl at Hh
  wp_auto
  wp_apply (h s _ σ txid Hcan) $$ [Hsh] as Hsh
  · iframe
  iapply HΦ
  unfold ownFL
  rw [show (σ.rollback txid).free = σ.free by unfold FLState.rollback; split <;> rfl]
  iframe Hhdl
  iframe
  try (iExactEq Hown; rfl)

theorem arrayImpl.freed (h : shared.Freed.spec (GF := GF) (hG := hG)) (a : Loc) :
    (arrayImpl (GF := GF) a).FreedSpec := by
  intro s σ id
  rw [arrayImpl.ity, arrayImpl.iv]
  wp_start as Hfl
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  ihave #Hh : arrayHdl (GF := GF) a s $$ [Hhdl]
  · iExactEq Hhdl; rfl
  iunfold arrayHdl at Hh
  wp_auto
  wp_apply (h s _ σ id) $$ [Hsh] as Hsh
  · iframe
  iapply HΦ
  unfold ownFL
  iframe Hhdl
  iframe
  try (iExactEq Hown; rfl)

theorem arrayImpl.pendingCount (h : shared.PendingCount.spec (GF := GF) (hG := hG)) (a : Loc) :
    (arrayImpl (GF := GF) a).PendingCountSpec := by
  intro s σ
  rw [arrayImpl.ity, arrayImpl.iv]
  wp_start as Hfl
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  ihave #Hh : arrayHdl (GF := GF) a s $$ [Hhdl]
  · iExactEq Hhdl; rfl
  iunfold arrayHdl at Hh
  wp_auto
  wp_apply (h s _ σ) $$ [Hsh] as Hsh
  · iframe
  iapply HΦ
  unfold ownFL
  iframe Hhdl
  iframe
  try (iExactEq Hown; rfl)

theorem arrayImpl.count (h : shared.Count.spec (GF := GF) (hG := hG)) (hFC : array.FreeCount.spec (GF := GF) (hG := hG)) (a : Loc) :
    (arrayImpl (GF := GF) a).CountSpec := by
  intro s σ
  rw [arrayImpl.ity, arrayImpl.iv]
  wp_start as Hfl
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  ihave #Hh : arrayHdl (GF := GF) a s $$ [Hhdl]
  · iExactEq Hhdl; rfl
  iunfold arrayHdl at Hh
  wp_auto
  wp_apply (h (arrayImpl a) s σ (arrayImpl.freeCountSpec hFC a)) $$ [Hsh Hown] as ⟨Hsh, Hown⟩
  · iframe
  iapply HΦ
  unfold ownFL
  iframe Hhdl
  iframe
  try (iExactEq Hown; rfl)

theorem arrayImpl.estimatedWritePageSize (h : shared.EstimatedWritePageSize.spec (GF := GF) (hG := hG)) (hFC : array.FreeCount.spec (GF := GF) (hG := hG)) (a : Loc) :
    (arrayImpl (GF := GF) a).EstimatedWritePageSizeSpec := by
  intro s σ
  rw [arrayImpl.ity, arrayImpl.iv]
  wp_start as Hfl
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  ihave #Hh : arrayHdl (GF := GF) a s $$ [Hhdl]
  · iExactEq Hhdl; rfl
  iunfold arrayHdl at Hh
  wp_auto
  wp_apply (h (arrayImpl a) s σ (arrayImpl.freeCountSpec hFC a)) $$ [Hsh Hown] as ⟨Hsh, Hown⟩
  · iframe
  unfold flCells
  iapply HΦ
  unfold ownFL
  iframe Hhdl
  iframe
  try (iExactEq Hown; rfl)

theorem arrayImpl.releasePending (h : shared.ReleasePendingPages.spec (GF := GF) (hG := hG)) (hM : array.mergeSpans.spec (GF := GF) (hG := hG)) (a : Loc) :
    (arrayImpl (GF := GF) a).ReleasePendingSpec := by
  intro s σ
  rw [arrayImpl.ity, arrayImpl.iv]
  wp_start as Hfl
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  ihave #Hh : arrayHdl (GF := GF) a s $$ [Hhdl]
  · iExactEq Hhdl; rfl
  iunfold arrayHdl at Hh
  wp_auto
  wp_apply (h (arrayImpl a) s σ (arrayImpl.mergeSpansSpec hM a)) $$ [Hsh Hown] as %σ' ⟨%He, Hsh, Hown⟩
  · iframe
    iexact Hhdl
  iapply HΦ
  unfold ownFL
  iframe Hhdl
  iframe
  try (iExactEq Hown; rfl)
  isplitr
  · ipureintro; exact He
  iExactEq Hown; rfl

theorem arrayImpl.read (h : shared.Read.spec (GF := GF) (hG := hG)) (hI : array.Init.spec (GF := GF) (hG := hG)) (a : Loc) :
    (arrayImpl (GF := GF) a).ReadSpec := by
  intro s σ p pv dq c xs dq2 Hnn Hfl0 Hov Hnd Hxs Hlen
  rw [arrayImpl.ity, arrayImpl.iv]
  wp_start as ⟨Hfl, Hp, Hcc, Hsl⟩
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  ihave #Hh : arrayHdl (GF := GF) a s $$ [Hhdl]
  · iExactEq Hhdl; rfl
  iunfold arrayHdl at Hh
  wp_auto
  wp_apply (h (arrayImpl a) s σ p pv dq c xs dq2 (arrayImpl.initSpec hI a) Hnn Hfl0 Hov Hnd Hxs Hlen)
    $$ [Hsh Hown Hp Hcc Hsl] as %fr ⟨%Hfr, Hsh, Hown, Hp, Hcc, Hsl⟩
  · iframe
    iexact Hhdl
  iapply HΦ
  unfold ownFL
  iframe Hhdl
  iframe
  try (iExactEq Hown; rfl)
  isplitr
  · ipureintro; exact Hfr
  iExactEq Hown; rfl

theorem arrayImpl.reload (h : shared.Reload.spec (GF := GF) (hG := hG)) (hI : array.Init.spec (GF := GF) (hG := hG)) (hFPI : array.freePageIds.spec (GF := GF) (hG := hG)) (a : Loc) :
    (arrayImpl (GF := GF) a).ReloadSpec := by
  intro s σ p pv dq c xs dq2 Hnn Hfl0 Hov Hnd Hxs Hlen
  rw [arrayImpl.ity, arrayImpl.iv]
  wp_start as ⟨Hfl, Hp, Hcc, Hsl⟩
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  ihave #Hh : arrayHdl (GF := GF) a s $$ [Hhdl]
  · iExactEq Hhdl; rfl
  iunfold arrayHdl at Hh
  wp_auto
  wp_apply (h (arrayImpl a) s σ p pv dq c xs dq2 (arrayImpl.initSpec hI a)
    (arrayImpl.freePageIdsSpec hFPI a) Hnn Hfl0 Hov Hnd Hxs Hlen)
    $$ [Hsh Hown Hp Hcc Hsl] as %fr ⟨%Hfr, Hsh, Hown, Hp, Hcc, Hsl⟩
  · iframe
    iexact Hhdl
  iapply HΦ
  unfold ownFL
  iframe Hhdl
  iframe
  try (iExactEq Hown; rfl)
  isplitr
  · ipureintro; exact Hfr
  iExactEq Hown; rfl

theorem arrayImpl.noSyncReload (h : shared.NoSyncReload.spec (GF := GF) (hG := hG)) (hI : array.Init.spec (GF := GF) (hG := hG)) (a : Loc) :
    (arrayImpl (GF := GF) a).NoSyncReloadSpec := by
  intro s σ pg xs dq Hinc Hge Hlen
  rw [arrayImpl.ity, arrayImpl.iv]
  wp_start as ⟨Hfl, Hpg⟩
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  ihave #Hh : arrayHdl (GF := GF) a s $$ [Hhdl]
  · iExactEq Hhdl; rfl
  iunfold arrayHdl at Hh
  wp_auto
  wp_apply (h (arrayImpl a) s σ pg xs dq iprop(pg ↦*{dq} xs) (arrayImpl.initSpec hI a) Hinc Hge Hlen)
    $$ [Hsh Hown Hpg] as ⟨Hsh, Hown, Hpg⟩
  · iframe
    isplitl []
    · iexact Hhdl
    iintro Hpg
    iframe
  simp only [decide_not]
  iapply HΦ
  unfold ownFL
  iframe Hhdl
  iframe
  try (iExactEq Hown; rfl)

theorem arrayImpl.ifaceFreeCount (h : array.FreeCount.spec (GF := GF) (hG := hG)) (a : Loc) :
    (arrayImpl (GF := GF) a).IfaceFreeCountSpec := by
  intro s σ
  rw [arrayImpl.ity, arrayImpl.iv]
  iintro %Φ ⟨#Hpkg, Hfl⟩ HΦ
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  iapply (h a s σ.free) $$ [Hown]
  · iExactEq Hown; rfl
  inext
  iintro Hown
  iapply HΦ
  unfold ownFL
  iframe Hhdl
  iframe
  iExactEq Hown; rfl

theorem arrayImpl.ifaceInit (h : array.Init.spec (GF := GF) (hG := hG)) (a : Loc) :
    (arrayImpl (GF := GF) a).IfaceInitSpec := by
  intro s σ ids xs Hwf
  rw [arrayImpl.ity, arrayImpl.iv]
  iintro %Φ ⟨#Hpkg, Hfl, Hids, Hcap⟩ HΦ
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  iapply (h a s σ ids xs Hwf) $$ [Hsh Hown Hids Hcap]
  · iframe
    isplitl []
    · iexact Hpkg
    isplitl []
    · iExactEq Hhdl; rfl
    iExactEq Hown; rfl
  inext
  iintro ⟨Hsh, Hown⟩
  iapply HΦ
  unfold ownFL
  iframe Hhdl
  iframe
  iExactEq Hown; rfl

theorem arrayImpl.write (h : shared.Write.spec (GF := GF) (hG := hG)) (hFC : array.FreeCount.spec (GF := GF) (hG := hG))
    (hFPI : array.freePageIds.spec (GF := GF) (hG := hG)) (a : Loc) :
    (arrayImpl (GF := GF) a).WriteSpec := by
  intro s σ p pv old Hnn Hold
  rw [arrayImpl.ity, arrayImpl.iv]
  wp_start as ⟨Hfl, Hp, Hsl⟩
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  ihave #Hh : arrayHdl (GF := GF) a s $$ [Hhdl]
  · iExactEq Hhdl; rfl
  iunfold arrayHdl at Hh
  wp_auto
  wp_apply (h (arrayImpl a) s σ p pv old (arrayImpl.freeCountSpec hFC a)
    (arrayImpl.freePageIdsSpec hFPI a) Hnn Hold) $$ [Hsh Hown Hp Hsl] as %out ⟨%Hout, Hsh, Hown, Hp, Hsl⟩
  · iframe
  iapply HΦ
  unfold ownFL
  iframe Hhdl
  iframe
  isplitr
  · ipureintro; exact Hout
  iExactEq Hown; rfl

/-- The `array` freelist at `a` meets the interface's contract, given the specs of its and
`shared`'s methods. -/
theorem arrayImpl.ifaceContract
    (hAdd : shared.AddReadonlyTXID.spec (GF := GF) (hG := hG)) (hRem : shared.RemoveReadonlyTXID.spec (GF := GF) (hG := hG))
    (hRel : shared.ReleasePendingPages.spec (GF := GF) (hG := hG)) (hAlloc : array.Allocate.spec (GF := GF) (hG := hG))
    (hFree : shared.Free.spec (GF := GF) (hG := hG)) (hRb : shared.Rollback.spec (GF := GF) (hG := hG)) (hFreed : shared.Freed.spec (GF := GF) (hG := hG))
    (hFC : array.FreeCount.spec (GF := GF) (hG := hG)) (hPC : shared.PendingCount.spec (GF := GF) (hG := hG))
    (hCount : shared.Count.spec (GF := GF) (hG := hG)) (hRead : shared.Read.spec (GF := GF) (hG := hG)) (hWrite : shared.Write.spec (GF := GF) (hG := hG))
    (hEst : shared.EstimatedWritePageSize.spec (GF := GF) (hG := hG)) (hReload : shared.Reload.spec (GF := GF) (hG := hG))
    (hNSR : shared.NoSyncReload.spec (GF := GF) (hG := hG)) (hInit : array.Init.spec (GF := GF) (hG := hG))
    (hFPI : array.freePageIds.spec (GF := GF) (hG := hG)) (hM : array.mergeSpans.spec (GF := GF) (hG := hG)) (a : Loc) :
    (arrayImpl (GF := GF) a).IfaceContract where
  addReadonly := arrayImpl.addReadonly hAdd a
  removeReadonly := arrayImpl.removeReadonly hRem a
  releasePending := arrayImpl.releasePending hRel hM a
  allocate := arrayImpl.allocate hAlloc a
  free := arrayImpl.free hFree a
  rollback := arrayImpl.rollback hRb a
  freed := arrayImpl.freed hFreed a
  freeCount := arrayImpl.ifaceFreeCount hFC a
  pendingCount := arrayImpl.pendingCount hPC a
  count := arrayImpl.count hCount hFC a
  read := arrayImpl.read hRead hInit a
  write := arrayImpl.write hWrite hFC hFPI a
  estimatedWritePageSize := arrayImpl.estimatedWritePageSize hEst hFC a
  reload := arrayImpl.reload hReload hInit hFPI a
  noSyncReload := arrayImpl.noSyncReload hNSR hInit a
  init := arrayImpl.ifaceInit hInit a

end proof

end bbolt
end EtcdGrove
end Perennial
