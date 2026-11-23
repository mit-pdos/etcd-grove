/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/client/BufferClient__Write.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`b.Write(key, val)`: a put, logically atomic over the abstract state (`linOwn`). Its
linearization point is not the client's step: it is the protocol step (a replica's) at which the
command is decided (`Spec/swift/Model.lean`, "The linearization"); the client's update is
deposited in `sp.inv` at its first send (`sp.client_register`) and committed there.
`Write` never fails: it returns once the put took effect, or never.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [client.Assumptions]

/-- `b.Write(key, val)` as client `cid`'s command of sequence number `s`: the put of
`val` (fewer than 2^16 bytes, `state.Value`'s length field) at `lin.keyName key`. -/
abbrev client.BufferClient.Write.spec : Prop :=
  ∀ (b : Loc) (γ : sp.Names) (γc γm γl : GName) (cid : w32) (s : Nat) (key : w64)
    (vsl : GoSlice) (v : List w8),
  ⊢ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client -∗
    client.ready b γ γc γm γl cid s -∗ vsl ↦*□ v -∗ ⌜v.length < 2 ^ 16 ∧ s < 2 ^ 10⌝ -∗
    <<{ ∀∀ σ, linOwn γl σ }>>
      (App (App (Val (b @!! go.GoType.PointerType client.BufferClient.ty @!! go!"Write"))
        (Val #key)) (Val #vsl)) @ ↑sp.spN
    <<{ linOwn γl (sp.lin.apply (sp.Cmd.put key v) σ).1 | RET #();
        client.ready b γ γc γm γl cid (s + 1) }>>

end spec

end Perennial.github_com.imdea_software.swiftpaxos
