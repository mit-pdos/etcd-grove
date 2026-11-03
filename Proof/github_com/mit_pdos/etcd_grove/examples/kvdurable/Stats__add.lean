/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Stats__add.lean`. Lean-first (no
Rocq counterpart; kvreconf's).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Stats__add

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

theorem Stats.add.wp_proof : Stats.add.spec (GF := GF) (hG := hG) := by
  intro s c
  wp_start as #Hc
  ihave #Hat : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  wp_auto
  wp_apply sync.atomic.Uint64.wp_Add c (W64 1) $$ [$Hat]
  iinv Hc with ⟨%v, >Hv⟩ Hclose
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ \ ↑kdStatsN from Std.LawfulSet.empty_subset)
  iintro Hmask
  inext
  iexists v
  iframe Hv
  iintro Hv
  imod Hmask with -
  imod Hclose $$ [Hv] with -
  · inext; iexists _; iexact Hv
  imodintro
  wp_auto
  iapply HΦ
  itrivial

end proof

end kvdurable
end EtcdGrove
end Perennial
