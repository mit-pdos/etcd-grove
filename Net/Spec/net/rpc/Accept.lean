/-
`rpc.Accept(lis)`: `DefaultServer.Accept(lis)` (`Server.Accept.spec` on `DefaultServer`, in any
registry mode: `defaultServerAny`). Lean-first.
-/
module

public import Net.Proof.net.rpc.ServerDefs
public import Perennial.Proof.log.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.rpc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.rpc.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev Accept.spec : Prop :=
  ∀ (γs : GName) (C : CodecSpec GF) (W : RpcWorld GF) (la : GoString)
    (lis : GoInterface) (l : w64),
  {{ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗ defaultServerAny γs ∗
      (□ ∀ a, ⌜addrOk a = true ∧ lisAccepts la a⌝ →
        rpcAddr (Gg := hG.goose_globalGS) W a ∗ srvServes γs C W a) ∗ srvEnv ∗ codecSet C ∗
      isPkgInit (PROP := IProp GF) pkg_id.log ∗
      net.isListener (GF := GF) lis l ∗ netLisOn (extLocalGS netExt (L := hG.goose_localGS)) l la ∗
      lisInv (Gg := hG.goose_globalGS) (extLocalGS netExt (L := hG.goose_localGS)) l la }}
    (App (Val (@! net.rpc.Accept)) (Val #lis))
  {{ RET #(); True }}

end spec
end net.rpc
end Perennial
