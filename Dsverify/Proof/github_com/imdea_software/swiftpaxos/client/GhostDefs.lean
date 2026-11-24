/-
The specs of `Ghost.lean` (the client package's prophecy-only helpers `resolveInvoke`, `resolveAccept`) that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.L2Laws
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.ISpecs
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.NodeGhost
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.NodeProph
public import Perennial.Proof.github_com.goose_lang.primitive.Link

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [client.Assumptions]

/-- `resolveInvoke(op, cl, seq, key, val)` (prophecy-only): client `cl` (predicted node
`cl (clOf x)`, whose prophecy is claimed) invokes command `x = (cl, seq)`, `c = (op, key, val)` with
its update: one resolution, `sp.encE (inv x c)`; registered, the update deposited (`pend`). -/
abbrev client.resolveInvoke.specG : Prop :=
  ∀ (γ : sp.Names) (γc γm γl : GName) (x : sp.CmdId) (c : sp.Cmd) (vsl : GoSlice)
    (Ψ : List w8 → IProp netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      client.nodeGhostB γ (sp.PNode.cl (sp.clOf x)) ∗ sp.inv γ γc γm γl ∗
      sp.allPredsReg γ γc ∗ sp.clientSeq γ x.cl x.seq.toNat ∗
      sp.cmdAU γl c Ψ ∗ vsl ↦*□ c.val ∗
      ⌜x.cl.toInt ≥ 1 ∧ (c.isPut ∨ c.isGet) ∧ c.val.length < 2 ^ 16 ∧ 0 ≤ x.seq.toInt ∧
        x.seq.toNat < 2 ^ 10⌝ }}
    (App (App (App (App (App (Val (@! client.resolveInvoke))
      (Val #c.op)) (Val #x.cl)) (Val #x.seq)) (Val #c.key)) (Val #vsl))
  {{ RET #(); sp.cmdIs γ x c ∗ sp.clientSeq γ x.cl (x.seq.toNat + 1) ∗ sp.pend γ x Ψ }}

/-- `resolveAccept(cl, seq, val)` (prophecy-only): client `cl` accepts command `x = (cl, seq)` with
its decided result `v` (one resolution, `sp.encE (resp x v)`): its continuation applied to `v`. -/
abbrev client.resolveAccept.specG : Prop :=
  ∀ (γ : sp.Names) (γc γm γl : GName) (x : sp.CmdId) (v : List w8)
    (vsl : GoSlice) (Ψ : List w8 → IProp netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      client.nodeGhostB γ (sp.PNode.cl (sp.clOf x)) ∗ sp.inv γ γc γm γl ∗ sp.pend γ x Ψ ∗
      sp.doneRes γ x v ∗ vsl ↦*□ v }}
    (App (App (App (Val (@! client.resolveAccept))
      (Val #x.cl)) (Val #x.seq)) (Val #vsl))
  {{ RET #(); ▷ Ψ v }}

set_option goose.wp.extras true

/-- The prophecy type is not an interface (for `MethodResolve` on `ProphId`'s value methods). -/
instance notInterface_prophId : go.NotInterface go.prophId := by
  unfold go.prophId; exact ⟨trivial⟩

end spec

end Perennial.github_com.imdea_software.swiftpaxos
