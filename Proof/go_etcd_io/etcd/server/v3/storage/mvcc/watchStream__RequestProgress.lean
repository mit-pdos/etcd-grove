/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchStream__RequestProgress
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.watchStream.RequestProgress.wp_proof :
    mvcc.watchStream.RequestProgress.spec (GF := GF) (hG := hG) := by
  intro ws wa P γ id
  wp_start as ⟨Hws, HPR⟩
  iunfold mvcc.isWatchStream at Hws
  iNamed Hws
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold mvcc.isWatchable at Hwable
  icases Hwable with ⟨%wi, %hwa, #Hwatch, #Hprog, #HprogAll, #Hrev⟩
  subst hwa
  iunfold mvcc.watchStreamInv at HR
  iNamed HR
  wp_auto
  wp_apply wp_map_lookup2 $$ [$Hwm] as Hwm
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HnextID Hclosed Hcf Hwf Hcm Hwm Hids Hcl]
  · inext
    iunfold mvcc.watchStreamInv
    iexists nextID, closed, cm, wm, CM, WM
    simp only [named]
    iframe
    iframe #
    ipureintro; exact ⟨Hdom, Hnn⟩
  cases hk : WM !! id with
  | none =>
    wp_auto
    iapply HΦ
    iframe HPR
  | some w =>
    simp only [Option.isSome_some, Option.getD_some]
    wp_auto
    wp_apply Hprog $$ [Hws $HPR] as HPR
    · icases Hws $$ %id %w %hk with ⟨$, -⟩
    iapply HΦ
    iframe HPR

/-- **The candidate `RequestProgress`** (`specC`): `spec`'s, the watchable store's reader borrowed
from the readers' pool for the thread token (`mvccBorrowW`, a credit of the call's first steps). -/
theorem mvcc.watchStream.RequestProgress.wp_proofC :
    mvcc.watchStream.RequestProgress.specC (GF := GF) (hG := hG) := by
  intro st γ ι id
  wp_start as ⟨#Hstr, Htt⟩
  iunfold mvcc.isMvccWatchStream at Hstr
  iunfold mvcc.isMvccWatchStreamI at Hstr
  icases Hstr with ⟨%Hn, #Hws, -, -, -, -, -, -, #Hwm⟩
  obtain ⟨-, hw, -⟩ := Hn
  iunfold mvcc.isWatchableMvccI at Hwm
  icases Hwm with ⟨-, %s, -, #Hmv⟩
  ihave %Hsl := mvcc.isMvccI_loc s γ $$ Hmv
  generalize (interface.mkOk (go.GoType.PointerType watchableStore.ty) #γ.wl : GoInterface) = wa
  iunfold mvcc.isWatchStream at Hws
  iNamed Hws
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto_lc 1
  imod mvcc.mvccBorrowW s γ hw $$ [$Hlc1 $Hmv $Htt] with ⟨HPR, Hback⟩
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold mvcc.isWatchable at Hwable
  icases Hwable with ⟨%wi, %hwa, #Hwatch, #Hprog, #HprogAll, #Hrev⟩
  subst hwa
  iunfold mvcc.watchStreamInv at HR
  iNamed HR
  wp_auto
  wp_apply wp_map_lookup2 $$ [$Hwm] as Hwm
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked HnextID Hclosed Hcf Hwf Hcm Hwm Hids Hcl]
  · inext
    iunfold mvcc.watchStreamInv
    iexists nextID, closed, cm, wm, CM, WM
    simp only [named]
    iframe
    iframe #
    ipureintro; exact ⟨Hdom, Hnn⟩
  iapply wp_fupd
  cases hk : WM !! id with
  | none =>
    wp_auto
    imod Hback $$ HPR with Htt
    imodintro
    iapply HΦ
    iframe Htt
  | some w =>
    simp only [Option.isSome_some, Option.getD_some]
    wp_auto
    wp_apply Hprog $$ [Hws HPR] as HPR
    · icases Hws $$ %id %w %hk with ⟨$, -⟩
      simp only [mvcc.storeWatchParams]
      rw [Hsl]
      iexact HPR
    simp only [mvcc.storeWatchParams]
    rw [Hsl]
    imod Hback $$ HPR with Htt
    imodintro
    iapply HΦ
    iframe Htt

end proof

end EtcdGrove
end Perennial
