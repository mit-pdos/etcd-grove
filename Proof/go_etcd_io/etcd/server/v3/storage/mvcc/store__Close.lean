/-
`store.Close` (`kvstore.go`, translated since 2026-10-22; the trust boundary until then): it closes
the store's `stopc` and stops its scheduler (`fifoSched.Stop()`), returning `nil`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Close
public import Spec.go_etcd_io.etcd.pkg.v3.schedule.Scheduler__Stop

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- The closer's share of the fields (at the pinned objects) reads `s.stopc` and `s.fifoSched`;
its stop channel's close right closes `stopc`; the scheduler's stop token and the compaction
queue's scheduler queue stop the scheduler. -/
theorem mvcc.store.Close.wp_proof
    (wp_Stop : schedule.Scheduler.Stop.spec (GF := GF) (hG := hG)) :
    mvcc.store.Close.spec (GF := GF) (hG := hG) := by
  intro s γ
  wp_start as ⟨#Hs, Hc⟩
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.schedule $$ []
  · iPkgInit
  ihave #Hs' := Hs
  iunfold mvcc.isStore at Hs'
  iNamed Hs'
  iunfold mvcc.storeCloser at Hc
  icases Hc with ⟨%o, Hfs, -, Hcl, Htok, Hq⟩
  -- the closer's share of the fields, at its objects (D22 receiver epochs, S5b: the current ones)
  iunfold mvcc.fieldShareAt at Hfs
  iNamed Hfs
  iunfold mvcc.physOk at Hph
  iNamed Hph
  iunfold mvcc.storeFields at Hflds
  iNamed Hflds
  obtain ⟨b, ti, ssched, sstop⟩ := o
  try simp only
  (try wp_auto)
  iunfold mvcc.stopCloser at Hcl
  icases Hcl with ⟨%γc, Hcl⟩
  wp_apply wp_broadcast_chan_close _ γc iprop(True) $$ [$Hcl] as -
  · imodintro; itrivial
  (try wp_auto)
  ihave #Hfifo' := HisSched
  iunfold schedule.isFifo at Hfifo'
  icases Hfifo' with ⟨%Hnn, -⟩
  cases ssched with
  | nil => exact absurd rfl Hnn
  | ok fi =>
  iunfold mvcc.compactQueue at Hq
  icases Hq with ⟨%Ps, %p, %Q, %R, Hq, -, -, -⟩
  (try wp_auto)
  wp_apply wp_Stop fi γ.sch (Ps ++ [p]) $$ [Htok Hq]
  · iframe; iframe #
  (try wp_auto)
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
