/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/api/snap/New.lean` (`snap.New`,
`snapshotter.go:34-43`): proved from its body. Claim #34, stage 4 (2026-11-23), once `snapshotterRO`
was defined (the `fsyncDir` field). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.snap.New
public import Spec.go_uber_org.zap.NewNop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode snap

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.snap.Assumptions]

theorem snap.New.wp_proof (hNewNop : zap.NewNop.spec (GF := GF) (hG := hG)) :
    snap.New.spec (GF := GF) (hG := hG) := by
  intro lg dir hdir
  wp_start as #Hlg0
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  iapply wp_fupd
  wp_auto
  -- `if lg == nil { lg = zap.NewNop() }`
  wp_join iprop(∃ l : Loc, "lg" ∷ lg_ptr ↦ l ∗ zapLoggerOk l) at next with [lg] as ⟨%l, lg, #Hl⟩
  · wp_if_destruct
    · wp_apply hNewNop as %l #Hlz
      (try wp_auto)
      wp_join_done
      iexists l; iframe; iexact Hlz
    · wp_join_done
      iexists lg; iframe
      iapply zapLoggerOrNil_ok _ Hif; iexact Hlg0
  iStructNamed «$r0»
  ipersist «lg»
  ipersist dir
  ipersist fsyncDir
  imodintro
  iapply HΦ
  unfold isSnapshotter snapshotterRO
  iframe #
  ipureintro; exact hdir
