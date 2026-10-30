/-
The `hashMap` freelist meets the freelist interface's contract `FLImpl.IfaceContract` (the
methods its users call), from the specs of `hashMap`'s and `shared`'s methods (`*hashMap`'s
promoted methods load its `shared` and call `shared`'s), and the specs of the methods `shared`
calls back (`FreeCount`, `freePageIds`, `mergeSpans`, and `Init` as `FLImpl.InitSpecW`).

Not `FLImpl.Contract`: its `FLImpl.InitSpec` (`Init` of any ids) does not hold for the
`hashMap`, whose `Init` of no ids returns before `reindex`, keeping the old cache (right only if
the old free ids were all pending): `hashMap.Init.spec`. The interface's specs that reach
`Init` (`Read`, `Reload`, `NoSyncReload`, `Init`) carry that condition.
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Iface
public import Proof.go_etcd_io.bbolt.internal.freelist.HashImpl
public import Spec.go_etcd_io.bbolt.internal.freelist.hashMap__FreeCount
public import Spec.go_etcd_io.bbolt.internal.freelist.hashMap__freePageIds
public import Spec.go_etcd_io.bbolt.internal.freelist.hashMap__Init
public import Spec.go_etcd_io.bbolt.internal.freelist.hashMap__mergeSpans
public import Spec.go_etcd_io.bbolt.internal.freelist.hashMap__Allocate
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

/-! The methods `shared` calls back. -/

theorem hashMapImpl.freeCountSpec (h : hashMap.FreeCount.spec (GF := GF) (hG := hG)) (a : Loc) :
    (hashMapImpl (GF := GF) a).FreeCountSpec := fun s free => h a s free

theorem hashMapImpl.freePageIdsSpec (h : hashMap.freePageIds.spec (GF := GF) (hG := hG)) (a : Loc) :
    (hashMapImpl (GF := GF) a).FreePageIdsSpec := by
  intro s free
  rw [hashMapImpl.ity, hashMapImpl.iv]
  iintro %Φ Hown HΦ
  iapply (h a s free) $$ [Hown]
  · iExactEq Hown; rfl
  inext
  iintro %r ⟨Hr, Hown⟩
  iapply HΦ
  iframe
  iintro -
  iExactEq Hown; rfl

theorem hashMapImpl.initSpecW (h : hashMap.Init.spec (GF := GF) (hG := hG)) (a : Loc) :
    (hashMapImpl (GF := GF) a).InitSpecW := fun s σ ids xs Hwf Hemp => h a s σ ids xs Hwf Hemp

theorem hashMapImpl.mergeSpansSpec (h : hashMap.mergeSpans.spec (GF := GF) (hG := hG)) (a : Loc) :
    (hashMapImpl (GF := GF) a).MergeSpansSpec :=
  fun s free ids ys h1 h2 h3 => h a s free ids ys h1 h2 h3

/-! The methods the freelist's users call. -/

theorem hashMapImpl.addReadonly (h : shared.AddReadonlyTXID.spec (GF := GF) (hG := hG)) (a : Loc) :
    (hashMapImpl (GF := GF) a).AddReadonlySpec := by
  intro s σ tid
  rw [hashMapImpl.ity, hashMapImpl.iv]
  wp_start as Hfl
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  ihave #Hh : hashHdl (GF := GF) a s $$ [Hhdl]
  · iExactEq Hhdl; rfl
  iunfold hashHdl at Hh
  wp_auto
  wp_apply (h s _ σ tid) $$ [Hsh] as Hsh
  · iframe
  iapply HΦ
  unfold ownFL
  iframe
  iexact Hhdl

theorem hashMapImpl.allocate (h : hashMap.Allocate.spec (GF := GF) (hG := hG)) (a : Loc) :
    (hashMapImpl (GF := GF) a).AllocateSpec := by
  intro s σ txid n Hn
  rw [hashMapImpl.ity, hashMapImpl.iv]
  exact h a s σ txid n Hn

theorem hashMapImpl.removeReadonly (h : shared.RemoveReadonlyTXID.spec (GF := GF) (hG := hG)) (a : Loc) :
    (hashMapImpl (GF := GF) a).RemoveReadonlySpec := by
  intro s σ tid
  rw [hashMapImpl.ity, hashMapImpl.iv]
  wp_start as Hfl
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  ihave #Hh : hashHdl (GF := GF) a s $$ [Hhdl]
  · iExactEq Hhdl; rfl
  iunfold hashHdl at Hh
  wp_auto
  wp_apply (h s _ σ tid) $$ [Hsh] as %ro ⟨%Hro, Hsh⟩
  · iframe
  iapply HΦ
  unfold ownFL
  iframe Hhdl
  iframe
  try (iExactEq Hown; rfl)
  ipureintro; exact Hro

theorem hashMapImpl.free (h : shared.Free.spec (GF := GF) (hG := hG)) (a : Loc) :
    (hashMapImpl (GF := GF) a).FreeSpec := by
  intro s σ txid p pv dq Hcan
  rw [hashMapImpl.ity, hashMapImpl.iv]
  wp_start as ⟨Hfl, Hp⟩
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  ihave #Hh : hashHdl (GF := GF) a s $$ [Hhdl]
  · iExactEq Hhdl; rfl
  iunfold hashHdl at Hh
  wp_auto
  wp_apply (h s _ σ txid p pv dq Hcan) $$ [Hsh Hp] as ⟨Hsh, Hp⟩
  · iframe
  iapply HΦ
  unfold ownFL
  iframe Hhdl
  iframe
  try (iExactEq Hown; rfl)

theorem hashMapImpl.rollback (h : shared.Rollback.spec (GF := GF) (hG := hG)) (a : Loc) :
    (hashMapImpl (GF := GF) a).RollbackSpec := by
  intro s σ txid Hcan
  rw [hashMapImpl.ity, hashMapImpl.iv]
  wp_start as Hfl
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  ihave #Hh : hashHdl (GF := GF) a s $$ [Hhdl]
  · iExactEq Hhdl; rfl
  iunfold hashHdl at Hh
  wp_auto
  wp_apply (h s _ σ txid Hcan) $$ [Hsh] as Hsh
  · iframe
  iapply HΦ
  unfold ownFL
  rw [show (σ.rollback txid).free = σ.free by unfold FLState.rollback; split <;> rfl]
  iframe Hhdl
  iframe
  try (iExactEq Hown; rfl)

theorem hashMapImpl.freed (h : shared.Freed.spec (GF := GF) (hG := hG)) (a : Loc) :
    (hashMapImpl (GF := GF) a).FreedSpec := by
  intro s σ id
  rw [hashMapImpl.ity, hashMapImpl.iv]
  wp_start as Hfl
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  ihave #Hh : hashHdl (GF := GF) a s $$ [Hhdl]
  · iExactEq Hhdl; rfl
  iunfold hashHdl at Hh
  wp_auto
  wp_apply (h s _ σ id) $$ [Hsh] as Hsh
  · iframe
  iapply HΦ
  unfold ownFL
  iframe Hhdl
  iframe
  try (iExactEq Hown; rfl)

theorem hashMapImpl.pendingCount (h : shared.PendingCount.spec (GF := GF) (hG := hG)) (a : Loc) :
    (hashMapImpl (GF := GF) a).PendingCountSpec := by
  intro s σ
  rw [hashMapImpl.ity, hashMapImpl.iv]
  wp_start as Hfl
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  ihave #Hh : hashHdl (GF := GF) a s $$ [Hhdl]
  · iExactEq Hhdl; rfl
  iunfold hashHdl at Hh
  wp_auto
  wp_apply (h s _ σ) $$ [Hsh] as Hsh
  · iframe
  iapply HΦ
  unfold ownFL
  iframe Hhdl
  iframe
  try (iExactEq Hown; rfl)

theorem hashMapImpl.count (h : shared.Count.spec (GF := GF) (hG := hG)) (hFC : hashMap.FreeCount.spec (GF := GF) (hG := hG)) (a : Loc) :
    (hashMapImpl (GF := GF) a).CountSpec := by
  intro s σ
  rw [hashMapImpl.ity, hashMapImpl.iv]
  wp_start as Hfl
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  ihave #Hh : hashHdl (GF := GF) a s $$ [Hhdl]
  · iExactEq Hhdl; rfl
  iunfold hashHdl at Hh
  wp_auto
  wp_apply (h (hashMapImpl a) s σ (hashMapImpl.freeCountSpec hFC a)) $$ [Hsh Hown] as ⟨Hsh, Hown⟩
  · iframe
  iapply HΦ
  unfold ownFL
  iframe Hhdl
  iframe
  try (iExactEq Hown; rfl)

theorem hashMapImpl.estimatedWritePageSize (h : shared.EstimatedWritePageSize.spec (GF := GF) (hG := hG)) (hFC : hashMap.FreeCount.spec (GF := GF) (hG := hG)) (a : Loc) :
    (hashMapImpl (GF := GF) a).EstimatedWritePageSizeSpec := by
  intro s σ
  rw [hashMapImpl.ity, hashMapImpl.iv]
  wp_start as Hfl
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  ihave #Hh : hashHdl (GF := GF) a s $$ [Hhdl]
  · iExactEq Hhdl; rfl
  iunfold hashHdl at Hh
  wp_auto
  wp_apply (h (hashMapImpl a) s σ (hashMapImpl.freeCountSpec hFC a)) $$ [Hsh Hown] as ⟨Hsh, Hown⟩
  · iframe
  unfold flCells
  iapply HΦ
  unfold ownFL
  iframe Hhdl
  iframe
  try (iExactEq Hown; rfl)

theorem hashMapImpl.releasePending (h : shared.ReleasePendingPages.spec (GF := GF) (hG := hG)) (hM : hashMap.mergeSpans.spec (GF := GF) (hG := hG)) (a : Loc) :
    (hashMapImpl (GF := GF) a).ReleasePendingSpec := by
  intro s σ
  rw [hashMapImpl.ity, hashMapImpl.iv]
  wp_start as Hfl
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  ihave #Hh : hashHdl (GF := GF) a s $$ [Hhdl]
  · iExactEq Hhdl; rfl
  iunfold hashHdl at Hh
  wp_auto
  wp_apply (h (hashMapImpl a) s σ (hashMapImpl.mergeSpansSpec hM a)) $$ [Hsh Hown] as %σ' ⟨%He, Hsh, Hown⟩
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

theorem hashMapImpl.read (h : shared.Read.spec (GF := GF) (hG := hG)) (hI : hashMap.Init.spec (GF := GF) (hG := hG)) (a : Loc) :
    (hashMapImpl (GF := GF) a).ReadSpec := by
  intro s σ p pv dq c xs dq2 Hnn Hfl0 Hov Hnd Hxs Hlen Hemp
  rw [hashMapImpl.ity, hashMapImpl.iv]
  wp_start as ⟨Hfl, Hp, Hcc, Hsl⟩
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  icases ownShared_wf _ _ _ $$ Hsh with ⟨Hsh, %Hwf⟩
  ihave Hsh := ownShared_w _ _ _ $$ Hsh
  ihave #Hh : hashHdl (GF := GF) a s $$ [Hhdl]
  · iExactEq Hhdl; rfl
  iunfold hashHdl at Hh
  wp_auto
  wp_apply (h (hashMapImpl a) s σ p pv dq c xs dq2 (hashMapImpl.initSpecW hI a) Hnn Hfl0 Hov Hnd
      (fun x hx => (Hxs x hx).1) Hlen (Hemp.imp id (fun h0 x hx => by rw [h0] at hx; cases hx)))
    $$ [Hsh Hown Hp Hcc Hsl] as %fr ⟨%Hfr, Hsh, Hown, Hp, Hcc, Hsl⟩
  · iframe
    iexact Hhdl
  icases ownSharedW_wfw _ _ _ $$ Hsh with ⟨Hsh, %Hwfw⟩
  ihave Hsh := (ownSharedW_wf _ _ _ (Hwfw.wf (fun x hx => (Hxs x (Hfr.2.mem_iff.1 hx)).2))) $$ Hsh
  iapply HΦ
  unfold ownFL
  iframe Hhdl
  iframe
  try (iExactEq Hown; rfl)
  isplitr
  · ipureintro; exact Hfr
  iExactEq Hown; rfl

theorem hashMapImpl.reload (h : shared.Reload.spec (GF := GF) (hG := hG)) (hI : hashMap.Init.spec (GF := GF) (hG := hG)) (hFPI : hashMap.freePageIds.spec (GF := GF) (hG := hG)) (a : Loc) :
    (hashMapImpl (GF := GF) a).ReloadSpec := by
  intro s σ p pv dq c xs dq2 Hnn Hfl0 Hov Hnd Hxs Hlen Hemp
  rw [hashMapImpl.ity, hashMapImpl.iv]
  wp_start as ⟨Hfl, Hp, Hcc, Hsl⟩
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  ihave Hsh := ownShared_w _ _ _ $$ Hsh
  ihave #Hh : hashHdl (GF := GF) a s $$ [Hhdl]
  · iExactEq Hhdl; rfl
  iunfold hashHdl at Hh
  wp_auto
  wp_apply (h (hashMapImpl a) s σ p pv dq c xs dq2 (hashMapImpl.initSpecW hI a)
    (hashMapImpl.freePageIdsSpec hFPI a) Hnn Hfl0 Hov Hnd Hxs Hlen
    (Hemp.imp id (fun h0 x hx => by rw [h0] at hx; cases hx)))
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

theorem hashMapImpl.noSyncReload (h : shared.NoSyncReload.spec (GF := GF) (hG := hG)) (hI : hashMap.Init.spec (GF := GF) (hG := hG)) (a : Loc) :
    (hashMapImpl (GF := GF) a).NoSyncReloadSpec := by
  intro s σ pg xs dq Hinc Hge Hlen Hemp
  rw [hashMapImpl.ity, hashMapImpl.iv]
  wp_start as ⟨Hfl, Hpg⟩
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  ihave Hsh := ownShared_w _ _ _ $$ Hsh
  ihave #Hh : hashHdl (GF := GF) a s $$ [Hhdl]
  · iExactEq Hhdl; rfl
  iunfold hashHdl at Hh
  wp_auto
  wp_apply (h (hashMapImpl a) s σ pg xs dq iprop(pg ↦*{dq} xs) (hashMapImpl.initSpecW hI a) Hinc Hge Hlen
      (Hemp.imp id (fun h0 x hx => by rw [h0] at hx; cases hx)))
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

theorem hashMapImpl.ifaceFreeCount (h : hashMap.FreeCount.spec (GF := GF) (hG := hG)) (a : Loc) :
    (hashMapImpl (GF := GF) a).IfaceFreeCountSpec := by
  intro s σ
  rw [hashMapImpl.ity, hashMapImpl.iv]
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

theorem hashMapImpl.ifaceInit (h : hashMap.Init.spec (GF := GF) (hG := hG)) (a : Loc) :
    (hashMapImpl (GF := GF) a).IfaceInitSpec := by
  intro s σ ids xs Hwf Hemp
  rw [hashMapImpl.ity, hashMapImpl.iv]
  iintro %Φ ⟨#Hpkg, Hfl, Hids, Hcap⟩ HΦ
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  ihave Hsh := ownShared_w _ _ _ $$ Hsh
  iapply (h a s σ ids xs Hwf.wfw (Hemp.imp id (fun h0 x hx => by rw [h0] at hx; cases hx)))
    $$ [Hsh Hown Hids Hcap]
  · iframe
    isplitl []
    · iexact Hpkg
    isplitl []
    · iExactEq Hhdl; rfl
    iExactEq Hown; rfl
  inext
  iintro ⟨Hsh, Hown⟩
  ihave Hsh := (ownSharedW_wf _ _ _ Hwf) $$ Hsh
  iapply HΦ
  unfold ownFL
  iframe Hhdl
  iframe
  iExactEq Hown; rfl

theorem hashMapImpl.write (h : shared.Write.spec (GF := GF) (hG := hG)) (hFC : hashMap.FreeCount.spec (GF := GF) (hG := hG))
    (hFPI : hashMap.freePageIds.spec (GF := GF) (hG := hG)) (a : Loc) :
    (hashMapImpl (GF := GF) a).WriteSpec := by
  intro s σ p pv old Hnn Hold
  rw [hashMapImpl.ity, hashMapImpl.iv]
  wp_start as ⟨Hfl, Hp, Hsl⟩
  iunfold ownFL at Hfl
  icases Hfl with ⟨#Hhdl, Hsh, Hown⟩
  ihave #Hh : hashHdl (GF := GF) a s $$ [Hhdl]
  · iExactEq Hhdl; rfl
  iunfold hashHdl at Hh
  wp_auto
  wp_apply (h (hashMapImpl a) s σ p pv old (hashMapImpl.freeCountSpec hFC a)
    (hashMapImpl.freePageIdsSpec hFPI a) Hnn Hold) $$ [Hsh Hown Hp Hsl] as %out ⟨%Hout, Hsh, Hown, Hp, Hsl⟩
  · iframe
  iapply HΦ
  unfold ownFL
  iframe Hhdl
  iframe
  isplitr
  · ipureintro; exact Hout
  iExactEq Hown; rfl

/-- The `hashMap` freelist at `a` meets the interface's contract, given the specs of its and
`shared`'s methods. -/
theorem hashMapImpl.ifaceContract
    (hAdd : shared.AddReadonlyTXID.spec (GF := GF) (hG := hG)) (hRem : shared.RemoveReadonlyTXID.spec (GF := GF) (hG := hG))
    (hRel : shared.ReleasePendingPages.spec (GF := GF) (hG := hG)) (hAlloc : hashMap.Allocate.spec (GF := GF) (hG := hG))
    (hFree : shared.Free.spec (GF := GF) (hG := hG)) (hRb : shared.Rollback.spec (GF := GF) (hG := hG)) (hFreed : shared.Freed.spec (GF := GF) (hG := hG))
    (hFC : hashMap.FreeCount.spec (GF := GF) (hG := hG)) (hPC : shared.PendingCount.spec (GF := GF) (hG := hG))
    (hCount : shared.Count.spec (GF := GF) (hG := hG)) (hRead : shared.Read.spec (GF := GF) (hG := hG)) (hWrite : shared.Write.spec (GF := GF) (hG := hG))
    (hEst : shared.EstimatedWritePageSize.spec (GF := GF) (hG := hG)) (hReload : shared.Reload.spec (GF := GF) (hG := hG))
    (hNSR : shared.NoSyncReload.spec (GF := GF) (hG := hG)) (hInit : hashMap.Init.spec (GF := GF) (hG := hG))
    (hFPI : hashMap.freePageIds.spec (GF := GF) (hG := hG)) (hM : hashMap.mergeSpans.spec (GF := GF) (hG := hG)) (a : Loc) :
    (hashMapImpl (GF := GF) a).IfaceContract where
  addReadonly := hashMapImpl.addReadonly hAdd a
  removeReadonly := hashMapImpl.removeReadonly hRem a
  releasePending := hashMapImpl.releasePending hRel hM a
  allocate := hashMapImpl.allocate hAlloc a
  free := hashMapImpl.free hFree a
  rollback := hashMapImpl.rollback hRb a
  freed := hashMapImpl.freed hFreed a
  freeCount := hashMapImpl.ifaceFreeCount hFC a
  pendingCount := hashMapImpl.pendingCount hPC a
  count := hashMapImpl.count hCount hFC a
  read := hashMapImpl.read hRead hInit a
  write := hashMapImpl.write hWrite hFC hFPI a
  estimatedWritePageSize := hashMapImpl.estimatedWritePageSize hEst hFC a
  reload := hashMapImpl.reload hReload hInit hFPI a
  noSyncReload := hashMapImpl.noSyncReload hNSR hInit a
  init := hashMapImpl.ifaceInit hInit a

end proof

end bbolt
end EtcdGrove
end Perennial
