/-
The definitions, specs and lemmas of `PoolFns.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.BatcherDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Perennial.Proof.sync.Link

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]

/-- The fast-ack pool, from swift's package state (`swift.pkgSt`). -/
def swift.FastAckPoolFact : Prop :=
  isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ⊢
    ∃ f : GoFunc, sync.isPool (globalAddr swift.fastAckPool) f iprop(True) swift.fastAckP ∗ ⌜f ≠ func.nil⌝

variable [swift.Assumptions]

/-- `newFastAck()` on a replica: a fresh or pooled `*MFastAck`, owned. -/
abbrev swift.newFastAck.specP : Prop :=
  ∀ (v : Bool),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      globalAddr swift.useFastAckPool ↦□ v }}
    (App (Val (@! swift.newFastAck)) (Val #()))
  {{ (l : Loc), RET #l; ∃ fa : swift.MFastAck, l ↦ fa }}

/-- `copyFastAck(fa)` on a replica: a fresh or pooled `*MFastAck` with `fa`'s fields. -/
abbrev swift.copyFastAck.specP : Prop :=
  ∀ (v : Bool) (l : Loc) (fa : swift.MFastAck),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      globalAddr swift.useFastAckPool ↦□ v ∗ l ↦□ fa }}
    (App (Val (@! swift.copyFastAck)) (Val #l))
  {{ (l' : Loc), RET #l'; l' ↦ fa }}

end specs

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [sync.Assumptions]

set_option goose.wp.extras true

/-- `IsNilDepOfCmdId(x, dep)`: whether `dep` is `[x]`. -/
theorem swift.IsNilDepOfCmdId.wp (x : swift.CommandId) (dep : GoSlice) (D : List swift.CommandId)
    (dq : DFrac) :
    {{ (dep ↦*{dq} D : IProp netDistGF) }}
      (App (App (Val (@! swift.IsNilDepOfCmdId)) (Val #x)) (Val #dep))
    {{ RET #(decide (D = [x])); dep ↦*{dq} D }} := by
  wp_start as Hd
  ihave %Hl := ownSlice_len _ _ _ $$ Hd
  wp_auto
  wp_if_destruct
  · have h1 : sint.nat (W64 1) = 1 := by decide
    obtain ⟨y, hy⟩ : ∃ y, D = [y] := by
      rcases D with _ | ⟨y, _ | ⟨z, t⟩⟩
      · exfalso; rw [Hif, h1] at Hl; simp at Hl
      · exact ⟨y, rfl⟩
      · exfalso; rw [Hif, h1] at Hl; simp at Hl
    subst hy
    rw [Hif]
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by decide⟩)]
    wp_apply wp_load_slice_index (t := swift.CommandId.ty) dep (sint.Z (W64 0)) [y] dq y (by decide) $$ [Hd] as Hd
    · iframe Hd; ipureintro; rfl
    try wp_auto
    wp_if_destruct
    · have e : decide (y.SeqNum' = x.SeqNum') = decide ([y] = [x]) := by
        cases x; cases y; simp_all
      rw [e]
      iapply HΦ
      iexact Hd
    · have e : decide ([y] = [x]) = false := by
        cases x; cases y; simp_all
      rw [e]
      iapply HΦ
      iexact Hd
  · have : D ≠ [x] := by
      intro h; subst h
      have e := swift.snat_eq dep.len Hl.2
      apply Hif; simp at Hl; word
    rw [decide_eq_false this]
    iapply HΦ
    iexact Hd

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
