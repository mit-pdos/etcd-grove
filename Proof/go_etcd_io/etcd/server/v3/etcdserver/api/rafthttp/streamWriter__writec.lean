/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/streamWriter__writec.lean`.
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamWriter__writec

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

theorem rafthttp.streamWriter.writec.wp_proof :
    rafthttp.streamWriter.writec.spec (GF := GF) (hG := hG) := by
  intro Rh ty lid pid Rr cw
  wp_start as #Hf
  iunfold swFixed at Hf
  icases Hf with ⟨%lg, %ps, %fs, %r, %γd, %cc, %sc, %dc, %γc, %γs, %γdn, -, -, -, -, -, -, -, -,
    -, -, #Hmu, -⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_with_defer as %defer defer
  wp_apply sync.Mutex.wp_Lock _ (swLockInv Rh ty lid pid cw) $$ [$Hmu] as ⟨Hlocked, Hinv⟩
  iunfold swLockInv at Hinv
  icases Hinv with ⟨%mc, %γm, %wk, %cl, Hmc, Hwk, Hcl, #Hbag⟩
  wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hmc Hwk Hcl]
  · inext
    iunfold swLockInv
    iexists mc, γm, wk, cl
    iframe; iframe #
  iapply HΦ
  iexists γm
  iexact Hbag

end proof

end EtcdGrove
end Perennial
