/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/PoolFns.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The fast-ack pool's functions on a replica (swift/defs.go:344-355): `releaseFastAck(f)` gives
`f` to `fastAckPool` when `useFastAckPool` is on, `newFastAck()` takes an `*MFastAck` from it
(or allocates one). On a replica node `useFastAckPool` is written once by `New` (`pl > 1`) and
then read-only (`↦□ v`, any `v`); the pool's predicate (`swift.fastAckP`: an owned `*MFastAck`)
is the package state's (`swift.pkgSt`, Proof/swift/Pkg.lean), taken here as the premise
`swift.FastAckPoolFact` (proved at the link from `pkgStates`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Batcher
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
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]

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
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [sync.Assumptions]

set_option goose.wp.extras true

theorem swift.releaseFastAck.wp_proof (hpool : swift.FastAckPoolFact (hG := hG)) :
    swift.releaseFastAck.specR (hG := hG) := by
  intro l v
  wp_start as ⟨#Hv, %fa, Hl⟩
  ihave #Hsw : isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift $$ []
  · iPkgInit
  have hp := hpool; unfold swift.FastAckPoolFact at hp
  ihave ⟨%f, #Hp, %Hfn⟩ := hp $$ Hsw
  wp_auto
  cases v
  · wp_auto
    iapply HΦ; itrivial
  · wp_auto
    wp_apply sync.Pool.wp_Put $$ [Hl]
    · iframe Hp
      iunfold swift.fastAckP
      iexists l, fa
      iframe Hl
      ipureintro; rfl
    try wp_auto
    iapply HΦ; itrivial

theorem swift.newFastAck.wp_proofP (hpool : swift.FastAckPoolFact (hG := hG)) :
    swift.newFastAck.specP (hG := hG) := by
  intro v
  wp_start as #Hv
  ihave #Hsw : isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift $$ []
  · iPkgInit
  have hp := hpool; unfold swift.FastAckPoolFact at hp
  ihave ⟨%f, #Hp, %Hfn⟩ := hp $$ Hsw
  wp_auto
  cases v
  · wp_auto
    iapply HΦ
    iexists _; iframe
  · wp_auto
    wp_apply sync.Pool.wp_Get $$ [$Hp] as %x ⟨Hx, -⟩
    icases Hx with (Hx | ⟨%Hf, -⟩)
    · iunfold swift.fastAckP at Hx
      icases Hx with ⟨%l, %fa, %Hxe, Hl⟩
      subst Hxe
      wp_auto
      iapply HΦ
      iexists fa; iframe
    · exact absurd Hf Hfn

theorem swift.copyFastAck.wp_proofP (wp_new : swift.newFastAck.specP (hG := hG)) :
    swift.copyFastAck.specP (hG := hG) := by
  intro v l fa
  wp_start as ⟨#Hpool, #Hl⟩
  ihave #Hf := Hl
  iStructNamed Hf
  wp_auto
  wp_apply wp_new as %l' ⟨%fa', Hl'⟩
  · iframe #
  try wp_auto
  iapply HΦ
  iExactEq Hl'
  cases fa; rfl

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
