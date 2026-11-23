/-
The definitions, specs and lemmas of `SHashes.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.HandlerInv
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.client.CmdKey
public import Perennial.Proof.bytes

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace swift.handler

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [bytes.Assumptions]

omit [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps] [swift.Assumptions] [bytes.Assumptions] in
/-- `slice_array` at any fraction. -/
theorem slice_array_dq {V : Type} [ZeroVal V] [TypedPointsto (GF := netDistGF) V] (l : Loc)
    (n : Int) (a : GoArray V n) (dq : DFrac) (hlen : a.arr.length < 2 ^ 63) :
    (typedPointsto l a dq : IProp netDistGF) ⊢ slice.mk l (W64 n) (W64 n) ↦*{dq} a.arr := by
  obtain ⟨arr⟩ := a
  iintro H
  icases array_len _ _ _ _ $$ H with %Hn
  rw [ownSlice_unseal]; unfold ownSliceDef
  iright
  have : sint.Z (W64 n) = n := by subst Hn; word
  simp only
  rw [this]
  iframe H
  ipureintro; omega

/-- `SHashesEq(hs1, hs2)`: true only if the lists are `SHashesEq` (`sp.shashesEq`). -/
abbrev SHashesEq.specI : Prop :=
  ∀ (s1 s2 : GoSlice) (l1 l2 : List sp.Hash),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      s1 ↦*□ l1.map shashOf ∗ s2 ↦*□ l2.map shashOf ∗
      ⌜(∀ h ∈ l1, h.length = 32) ∧ ∀ h ∈ l2, h.length = 32⌝ }}
    (App (App (Val (@! swift.SHashesEq)) (Val #s1)) (Val #s2))
  {{ (b : Bool), RET #b; ⌜b = true → sp.shashesEq l1 l2⌝ }}

/-- `Dep(d1).Equals(d2)` on nil dependencies (the handler's acks have none): returns. -/
abbrev Dep.Equals.specI : Prop :=
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift }}
    (App (Val (slice.nil @!! swift.Dep.ty @!! go!"Equals")) (Val #slice.nil))
  {{ (b : Bool), RET #b; True }}

end proof

end swift.handler

end Perennial.github_com.imdea_software.swiftpaxos
