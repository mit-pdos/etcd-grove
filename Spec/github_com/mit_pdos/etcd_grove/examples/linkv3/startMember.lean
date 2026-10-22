/-
`startMember(name, peer, peerAddr, client, cluster, lg)` (`examples/linkv3/linkv3.go`; D20, D21,
2026-10-19): one member of linkv3's cluster started -- putget3's `startMember`
(`Spec/.../putget3/startMember.lean`, whose header explains the triple) with linkv3's cluster
token, member names and URLs (`linkv3.bootPremise`, `linkv3.initURLs3`). Its success is putget3's
`memberUp`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3.Alloc
public import Spec.github_com.mit_pdos.etcd_grove.examples.putget3.startMember

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3

open Iris Iris.BI go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver
open putget3 (httpURL ccOk commonPremises memberBoot memberUp)

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv3.Assumptions]

/-- See the file header. -/
abbrev startMember.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] (N : Nat) (name peerAddr client : GoString)
    (peer : GoSlice) (cluster lg : Loc) (sl₁ sl₂ sl₃ : GoSlice)
    (ps : List w64) (bootLog : List EntryM) (dir : w64 → List GoString) (id : w64)
    (γ : RaftNames) (bud : BudgetNames) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (Φs : w64 → w64 → List w8 → GName → IProp GF) (γn : NetNames GF),
  threadBound GF ≤ 2 ^ 31 → receiptBound GF ≤ 2 ^ 48 → receiptBound GF ≤ N + 1 →
  γ.reCfg = GMap.listToSet ps → γ.reDyn = none → γ.reCCOk = ccOk ps → γ.reBoot = bootLog →
  γ.reNoSnap = true → bootLog.length ≤ 2 ^ 60 →
  γn.N = srvNet γ bud → γn.dir = dir → go!"http://" ++ peerAddr ∈ dir id →
  lg ≠ null →
  ckptEffectsOk → authRecordsFit → apply.backendUnderQuota → mvcc.backendNoCompaction →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkv3 ∗
      netAddrFree (GF := GF) peerAddr ∗ threadTok ∗
      peer ↦*□ [httpURL peerAddr] ∗
      cluster ↦$□ GMap.insert name₃ sl₃ (GMap.insert name₂ sl₂ (GMap.insert name₁ sl₁ ∅)) ∗
      sl₁ ↦*□ initURLs3 name₁ ∗ sl₂ ↦*□ initURLs3 name₂ ∗ sl₃ ↦*□ initURLs3 name₃ ∗
      bootPremise N ps bootLog dir name peerAddr client id ∗ commonPremises ∗
      context.isClosedchanInit ∗
      memberBoot putgetWorkload γ bud bootLog ρ E₀ Φs id ∗ netSlot γn id }}
    (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.linkv3.startMember))
      (Val #name)) (Val #peer)) (Val #peerAddr)) (Val #client)) (Val #cluster)) (Val #lg))
  {{ (s : Loc) (err : GoInterface), RET (PairV #s #err);
      (⌜err ≠ GoInterface.nil⌝ ∗ threadTok) ∨ (⌜err = GoInterface.nil⌝ ∗ memberUp s ρ E₀ lg) }}

end spec

end linkv3
end EtcdGrove
end Perennial
