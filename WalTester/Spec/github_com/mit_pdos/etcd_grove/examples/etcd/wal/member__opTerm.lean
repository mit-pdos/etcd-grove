/-
`(*member).opTerm()` (wal.go) over `fsExt` (W4c U5): a term change (`tNextTerm`: the term raised by one below
`maxIndex = 2^62`) with any vote, then `save` of the member's hard state with no entries: `save`'s
postcondition (`memSavePost`) at that hard state. The stored oracles' size premise is over any hard state
(an operation's encoding length does not depend on its hard state's values). Lean-first (no Rocq
counterpart). The fields' relation to the history's discipline (`tMemSim`, with the member's `base` and
`last` values `bs`, `l`) is kept (tenth session).
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.MemberRep
public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.MemberSim

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.wal Fs WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

/-- See the file header. -/
abbrev member.opTerm.spec : Prop :=
  ∀ (W : WalGS GF) (e : TEnv) (γ : TGS) (m w : Loc) (v : oracle) (o os : TOracle) (c : TCand)
    (d : WalDur) (qc : Qp) (t vo cm bs l : w64) (r : Loc) (rv : rnd),
  e.orFile.Ok → tMemOk o c d → tMemHs o d → uint.nat t < 2 ^ 63 → tMemSim o c bs l cm →
  (∀ h : THs, tOrSmall (tSaveO1 o h []) ∧ tOrSmall (tSynced (tSaveO1 o h []))) → tCheckWf o →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      memSaveRes W e γ m w v o os c d qc ∗
      m.[member, go!"term"] ↦ t ∗ m.[member, go!"vote"] ↦ vo ∗ m.[member, go!"commit"] ↦ cm ∗
      m.[member, go!"r"] ↦ r ∗ r ↦ rv }}
    (App (Val (m @!! go.GoType.PointerType member.ty @!! go!"opTerm")) (Val #()))
  {{ (b : Bool), RET #b; ∃ vo' : w64,
      m.[member, go!"term"] ↦ tNextTerm t ∗ m.[member, go!"vote"] ↦ vo' ∗ m.[member, go!"commit"] ↦ cm ∗
      m.[member, go!"r"] ↦ r ∗ (∃ rv' : rnd, r ↦ rv') ∗
      memSavePost W e γ m w o c qc (hardState.mk (tNextTerm t) vo' cm) [] b ∗
      ⌜tMemSim (tSaveO o (hardState.mk (tNextTerm t) vo' cm) []) c bs l cm⌝ }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
