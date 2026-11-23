/-
The definitions, specs and lemmas of `DepHash.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DepHashPure
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HandleSync
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HashLogSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.KeyDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SliceNN

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]
variable [swift.Assumptions]

/-- `keysOf(cmd)` of a command that is not a scan: its key. -/
abbrev swift.keysOf.specNS : Prop :=
  ∀ (op : w8) (k : w64) (vs : GoSlice),
  {{ (⌜op ≠ W8 3⌝ : IProp netDistGF) }}
    (App (Val (@! swift.keysOf)) (Val #(state.Command.mk op k vs)))
  {{ (sl : GoSlice), RET #sl; sl ↦* [k] }}

end specs

section helpers
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [π : NetProtoGS]

/-- One entry of a map's big separating conjunction changes its predicate (the others' imply
the new one). -/
theorem swift.bigSepM_change1 {V : Type} (m : GMap w64 V) (k : w64) (v : V)
    (Φ Ψ : w64 → V → IProp netDistGF) (hk : m.lookup k = some v)
    (h : ∀ k' v', k' ≠ k → Φ k' v' ⊢ Ψ k' v') :
    ([∗map] k' ↦ v' ∈ m, Φ k' v') ⊢ Φ k v ∗ (Ψ k v -∗ [∗map] k' ↦ v' ∈ m, Ψ k' v') := by
  iintro Hm
  ihave ⟨Hk, Hr⟩ := (BigSepM.bigSepM_delete (Φ := Φ) (show get? m k = some v from hk)).1 $$ Hm
  iframe Hk
  iintro Hk
  iapply (BigSepM.bigSepM_delete (Φ := Ψ) (show get? m k = some v from hk)).2
  iframe Hk
  iapply (BigSepM.bigSepM_mono (Φ := Φ) (Ψ := Ψ) (m := Iris.Std.PartialMap.delete m k)
    (fun {k' v'} hk' => h k' v' (by
      intro he; subst he
      rw [Iris.Std.LawfulPartialMap.get?_delete_eq rfl] at hk'
      cases hk')))
  iexact Hr

/-- A new entry. -/
theorem swift.bigSepM_add1 {V : Type} (m : GMap w64 V) (k : w64) (v : V)
    (Φ Ψ : w64 → V → IProp netDistGF) (hk : m.lookup k = none)
    (h : ∀ k' v', k' ≠ k → Φ k' v' ⊢ Ψ k' v') :
    ([∗map] k' ↦ v' ∈ m, Φ k' v') ⊢ Ψ k v -∗ [∗map] k' ↦ v' ∈ Iris.Std.PartialMap.insert m k v, Ψ k' v' := by
  iintro Hm Hk
  iapply (BigSepM.bigSepM_insert (Φ := Ψ) (show get? m k = none from hk)).2
  iframe Hk
  iapply (BigSepM.bigSepM_mono (Φ := Φ) (Ψ := Ψ) (m := m)
    (fun {k' v'} hk' => h k' v' (by
      intro he; subst he
      have : get? m k' = none := hk
      rw [this] at hk'; cases hk')))
  iexact Hm

end helpers

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

set_option goose.wp.extras true

end proofs

section link
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions] [crypto.sha256.Assumptions] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]

end link

end Perennial.github_com.imdea_software.swiftpaxos
