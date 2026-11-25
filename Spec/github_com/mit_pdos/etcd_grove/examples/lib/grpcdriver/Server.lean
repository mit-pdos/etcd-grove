/- Lean-first (no Rocq counterpart).

`Server()`: on a machine where the deployment set the address `drvAddr` to serve the driver's table
(`grpcAddrAt drvAddr (drvSvc γid)`) and keeps its listening token in its invariant (`lisTokN`), builds the gRPC server (no options), registers the driver's service on a fresh
`server`, listens at `drvAddr` and serves; returns only if it cannot listen, or when `Serve` returns.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.ServerDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.ListenSet

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- See the file header. -/
abbrev Server.spec : Prop :=
  ∀ [hX : HasExt netExt] (π : NetProtoGS) (σ : NetSlotGS) (γid : GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver ∗
      inv (lisTokN drvAddr) (netLisTok (NG (Gg := hG.goose_globalGS)) drvAddr) ∗
      grpcAddrAt (Gg := hG.goose_globalGS) (π := π) (σ := σ) drvAddr (drvSvc γid) }}
    (App (Val (@! Server)) (Val #()))
  {{ RET #(); True }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
