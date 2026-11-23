/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/config/Defs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The configuration struct the adapter builds (`kit.go`'s `nodeConfig`) as the master and the
replicas read it: no quorum file, no proxies (an empty `ProxyInfo`), no fixed leader.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- `p` is `nodeConfig`'s `*config.Config` (persistent, read only): `Quorum` empty, no fixed
`Leader`, `Optread` the fast-read flag `fr`, an empty `ProxyInfo`. -/
def config.plain (p : Loc) (fr : Bool) : IProp GF :=
  iprop(∃ (v : config.Config) (pi : config.ProxyInfo), p ↦□ v ∗ v.Proxy' ↦□ pi ∗
    ⌜p ≠ null ∧ v.Proxy' ≠ null ∧ v.Quorum' = [] ∧ v.Leader' = null ∧ v.Optread' = fr ∧
      pi.locals' = null ∧ pi.proxies' = null ∧ pi.servers' = null⌝)

instance config.plain_persistent (p : Loc) (fr : Bool) : Persistent (config.plain (GF := GF) p fr) := by
  unfold config.plain; infer_instance

end defs

end Perennial.github_com.imdea_software.swiftpaxos
