/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/ISpecs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The client package's internal specs (notes/prove-clientpkg.md): the triples its functions are
proved against, over the internal predicates of `Proof/client/Defs.lean`.

* `Client.SendWrite.specI`, `Client.SendRead.specI`: the next command (sequence number `s`,
  registered: `cmdIs`) sent to every writer; the sequence number field advanced.
* `BufferClient.Write.specI`, `BufferClient.Read.specI`: the frozen `Write`/`Read` specs over
  `readyI` (HUB-REQUEST 1).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Defs
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

/-- `cl.SendProposal(p)`: the proposal (registered: `cmdIs`) framed on every writer. -/
abbrev client.Client.SendProposal.specI : Prop :=
  ∀ (cl : Loc) (γ : sp.Names) (γc γm : GName) (cid : w32) (N : Nat)
    (pv : replica.defs.Propose) (seq : w32) (c : sp.Cmd),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      client.sendSt γ γc γm cl cid N ∗ pv.Command'.V' ↦*□ c.val ∗ sp.cmdIs γ ⟨cid, seq⟩ c ∗
      ⌜pv.CommandId' = seq ∧ pv.ClientId' = cid ∧ pv.Command'.Op' = c.op ∧
        pv.Command'.K' = c.key ∧ pv.Timestamp' = W64 0 ∧ c.val.length < 2 ^ 16⌝ }}
    (App (Val (cl @!! go.GoType.PointerType client.Client.ty @!! go!"SendProposal")) (Val #pv))
  {{ RET #(); client.sendSt γ γc γm cl cid N }}

/-- `cl.SendWrite(key, val)`: the put of `val` at `key` as command `s` (registered). -/
abbrev client.Client.SendWrite.specI : Prop :=
  ∀ (cl : Loc) (γ : sp.Names) (γc γm : GName) (cid : w32) (N s : Nat) (key : w64)
    (vsl : GoSlice) (v : List w8),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      structFieldRef client.Client go!"seqnum" cl ↦ W32 ((s : Int) - 1) ∗
      client.sendSt γ γc γm cl cid N ∗ vsl ↦*□ v ∗
      sp.cmdIs γ ⟨cid, W32 (s : Int)⟩ (sp.Cmd.put key v) ∗ ⌜v.length < 2 ^ 16⌝ }}
    (App (App (Val (cl @!! go.GoType.PointerType client.Client.ty @!! go!"SendWrite"))
      (Val #key)) (Val #vsl))
  {{ RET #(W32 (s : Int)); structFieldRef client.Client go!"seqnum" cl ↦ W32 (s : Int) ∗
      client.sendSt γ γc γm cl cid N }}

/-- `cl.SendRead(key)`: the get of `key` as command `s` (registered). -/
abbrev client.Client.SendRead.specI : Prop :=
  ∀ (cl : Loc) (γ : sp.Names) (γc γm : GName) (cid : w32) (N s : Nat) (key : w64),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      structFieldRef client.Client go!"seqnum" cl ↦ W32 ((s : Int) - 1) ∗
      client.sendSt γ γc γm cl cid N ∗ sp.cmdIs γ ⟨cid, W32 (s : Int)⟩ (sp.Cmd.get key) }}
    (App (Val (cl @!! go.GoType.PointerType client.Client.ty @!! go!"SendRead")) (Val #key))
  {{ RET #(W32 (s : Int)); structFieldRef client.Client go!"seqnum" cl ↦ W32 (s : Int) ∗
      client.sendSt γ γc γm cl cid N }}

/-- `Write.spec` over `readyI`. -/
abbrev client.BufferClient.Write.specI : Prop :=
  ∀ (b : Loc) (γ : sp.Names) (γc γm γl : GName) (cid : w32) (s : Nat) (key : w64)
    (vsl : GoSlice) (v : List w8),
  ⊢ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client -∗
    client.ready b γ γc γm γl cid s -∗ vsl ↦*□ v -∗ ⌜v.length < 2 ^ 16 ∧ s < 2 ^ 25⌝ -∗
    <<{ ∀∀ σ, linOwn γl σ }>>
      (App (App (Val (b @!! go.GoType.PointerType client.BufferClient.ty @!! go!"Write"))
        (Val #key)) (Val #vsl)) @ ↑sp.spN
    <<{ linOwn γl (sp.lin.apply (sp.Cmd.put key v) σ).1 | RET #();
        client.ready b γ γc γm γl cid (s + 1) }>>

/-- `Read.spec` over `readyI`. -/
abbrev client.BufferClient.Read.specI : Prop :=
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
