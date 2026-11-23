/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/client/BufferClient__Read.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`b.Read(key)`: a get, logically atomic over the abstract state (`linOwn`), its linearization
point a replica's step (as `Write`'s). Returns the key's value at that point (empty if none),
or never.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.Defs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [client.Assumptions]

/-- `b.Read(key)` as client `cid`'s command of sequence number `s`: the value of
`lin.keyName key` in the abstract state at the linearization point (read-only: the slice is
shared with the reply it came in). -/
abbrev client.BufferClient.Read.spec : Prop :=
  ∀ (b : Loc) (γ : sp.Names) (γc γm γl : GName) (cid : w32) (s : Nat) (key : w64),
  ⊢ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client -∗
    client.ready b γ γc γm γl cid s -∗ ⌜s < 2 ^ 25⌝ -∗
    <<{ ∀∀ σ, linOwn γl σ }>>
      (App (Val (b @!! go.GoType.PointerType client.BufferClient.ty @!! go!"Read")) (Val #key))
      @ ↑sp.spN
    <<{ linOwn γl σ | (sl : GoSlice), RET #sl;
        sl ↦*□ (σ (lin.keyName key)).getD [] ∗ client.ready b γ γc γm γl cid (s + 1) }>>

end spec

end Perennial.github_com.imdea_software.swiftpaxos
