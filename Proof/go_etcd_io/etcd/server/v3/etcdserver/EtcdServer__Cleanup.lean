/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__Cleanup.lean` (the restart plan's
R2b-3c part 2b, 2026-11-04). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Cleanup
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Stop
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__Close
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__Close

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.Cleanup.wp_proof
    (hLS : lease.lessor.Stop.spec (GF := GF) (hG := hG))
    (hKC : mvcc.watchableStore.Close.spec (GF := GF) (hG := hG))
    (hBC : backend.backend.Close.spec (GF := GF) (hG := hG)) :
    EtcdServer.Cleanup.spec (GF := GF) (hG := hG) := by
  intro s lp wsl st γw c stl K γbe d dq W Pk cp X Y
  wp_start as ⟨#Hlf, Hstop, #Hkvf, #Hws, Hwcl, #Hauf, #HaC, Htpa, Hbr, Hbe, Hγbe, #Hb, #Hsc, Hopen,
    HX, #Hreq, #Hcpf, #Hcpok⟩
  (try wp_auto)
  -- `s.lessor.Stop()`
  ihave #Hlpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease $$ []
  · iPkgInit
  wp_apply (hLS lp) $$ [$Hstop]
  (try wp_auto)
  -- `s.kv.Close()`
  ihave #Hmpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  -- `Close` gives back the loops' readers and the compaction job's resource: with the caller's
  -- census, the backend's whole open token (R2b-3d stage 5c; until then dropped here)
  wp_apply (hKC wsl st γw c) $$ [$Hwcl] as ⟨Hlrs, Hjob⟩
  · iframe #
  imod Hopen $$ [Hlrs Hjob] with Hopen
  · iunfold mvcc.wsCloseRes; iframe Hlrs Hjob
  (try wp_auto)
  -- `s.authStore.Close()`
  ihave #Hapkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth $$ []
  · iPkgInit
  iunfold authCloser at HaC
  wp_apply HaC $$ [$Hapkg $Htpa] as %aerr ⟨-, Htpa⟩
  (try wp_auto)
  -- `s.bemu.Lock(); s.be.Close(); s.bemu.Unlock()`: the lock's invariant kept whole (the apply
  -- side's half of `s.be` reads it)
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  iunfold srvBemuReaderAt at Hbr
  wp_apply sync.RWMutex.wp_Lock $$ [$Hbr] as ⟨Hbl, Hbm⟩
  (try wp_auto)
  ihave #Hbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  wp_apply (hBC d.γB d.P W Pk d.be X Y) $$ [$Hopen $HX] as %berr ⟨HY, %D, Hsv, Hres⟩
  · iframe #
  (try wp_auto)
  wp_apply sync.RWMutex.wp_Unlock $$ [$Hbl Hbm] as Hbr
  · iframe #; inext; iexact Hbm
  (try wp_auto)
  -- `s.compactor.Stop()`, if any
  iunfold compactorOk at Hcpok
  icases Hcpok with (%Hnil | ⟨%T, %P, #Hcok⟩)
  · subst Hnil
    (try wp_auto)
    iapply HΦ
    iunfold srvBemuReaderAt
    iframe Htpa Hbr Hbe Hγbe
    isplitl [HY]
    · iexact HY
    iexists D
    iframe Hsv
    icases Hres with (⟨-, Hf⟩ | %Hbad)
    · ileft; iexact Hf
    · iright; ipureintro; exact Hbad
  iunfold v3compactor.compactorOk at Hcok
  icases Hcok with ⟨%ci, %Hci, -, #HStop, -, -⟩
  subst Hci
  (try wp_auto)
  wp_bind (App (Val #(methods ci.ty go!"Stop" ci.v)) (Val #()))
  iapply HStop $$ [] [-]
  · itrivial
  inext
  iintro -
  (try wp_auto)
  iapply HΦ
  iunfold srvBemuReaderAt
  iframe Htpa Hbr Hbe Hγbe
  isplitl [HY]
  · iexact HY
  iexists D
  iframe Hsv
  icases Hres with (⟨-, Hf⟩ | %Hbad)
  · ileft; iexact Hf
  · iright; ipureintro; exact Hbad

end proof

end EtcdGrove
end Perennial
