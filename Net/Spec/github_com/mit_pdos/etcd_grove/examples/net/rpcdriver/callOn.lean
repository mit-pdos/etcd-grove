/- Lean-first (no Rocq counterpart).

`callOn(c, ids)`: random calls on the client `c` from at most `maxWorkers` (4) concurrent workers,
each making at most `maxCalls` (8), with `Call` or `Go` at random; each outcome checked (`check`).
It takes a credit per call (`ownToks γb`, 32), and the caller's thread token (the workers'
wait group is `sync.tokJoin`'s, as net/rpc's `ServeCodec`).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Defs
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Codec
public import Net.Spec.net.rpc.Client__Call

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- See the file header. -/
abbrev callOn.spec : Prop :=
  ∀ (γid γb : GName) (c ids : Loc) (W : net.rpc.RpcWorld GF) (a : GoString),
    W.SS a go!"Svc" = some (echoSvc γid) →
  {{ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗ drvFacts ∗ isPkgInit (PROP := IProp GF) pkg_id.strings ∗
      net.rpc.isClient c W a ∗ net.rpc.codecSet drvCodec ∗ isCtr γid γb ids ∗
      ownToks γb 32 ∗ threadTok }}
    (App (App (Val (@! callOn)) (Val #c)) (Val #ids))
  {{ RET #(); threadTok }}

end spec
end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
end Perennial
