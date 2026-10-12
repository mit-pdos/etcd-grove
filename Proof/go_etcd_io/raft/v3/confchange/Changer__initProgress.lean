/-
Proof of `Spec/Changer__initProgress.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.Changer__initProgress
public import Spec.go_etcd_io.raft.v3.confchange.incoming
public import Spec.go_etcd_io.raft.v3.tracker.NewInflights

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem confchange.Changer.initProgress.wp_proof
    (wp_confchange_incoming : confchange.incoming.spec (GF := GF) (hG := hG))
    (wp_tracker_NewInflights : tracker.NewInflights.spec (GF := GF) (hG := hG)) :
    confchange.Changer.initProgress.spec (GF := GF) (hG := hG) := by
  intro cfgp trk v chg cfg id vm prs Hcfg Hmi
  obtain ⟨⟨Harr, Hl, Hln⟩, Hal⟩ := Hcfg
  wp_start as ⟨Hcfgp, Hv, Htrk⟩
  wp_auto
  wp_apply wp_confchange_incoming _ v map.nil Harr
  wp_apply wp_mapInsert $$ Hv as Hv
  -- `max(c.LastIndex, 1)`: Goose's `max` is stepped into
  wp_func_call
  wp_call
  wp_if_destruct
  -- both branches of `max`: the fresh `Progress`, into the map, `StateProbe`
  all_goals
    wp_apply wp_tracker_NewInflights _ _ Hmi as %il Hinfl
    wp_apply wp_mapInsert $$ Htrk as Htrk
    iapply HΦ
    iframe Hcfgp Hv Htrk
    iapply ownProgress_of _ _ .probe _ rfl rfl $$ «$r0» Hinfl
