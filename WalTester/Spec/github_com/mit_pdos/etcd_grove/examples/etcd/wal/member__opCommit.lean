/-
`(*member).opCommit()` (wal.go) over `fsExt` (W4c U5): nothing if the commit is at the last index; else the
commit advanced to some `cm'` in `(cm, l]`, then `save` of the member's hard state with no entries
(`memSavePost` at it). The size premise as `opTerm`'s. Lean-first (no Rocq counterpart).
-/
module

public import WalTester.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.MemberRep

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
abbrev member.opCommit.spec : Prop :=
  ∀ (W : WalGS GF) (e : TEnv) (γ : TGS) (m w : Loc) (v : oracle) (o os : TOracle) (c : TCand)
    (d : WalDur) (qc : Qp) (t vo cm l : w64) (r : Loc) (rv : rnd),
  e.orFile.Ok → tMemOk o c d → tMemHs o d → uint.nat t < 2 ^ 63 →
  (∀ h : THs, tOrSmall (tSaveO1 o h []) ∧ tOrSmall (tSynced (tSaveO1 o h []))) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      memSaveRes W e γ m w v o os c d qc ∗
      m.[member, go!"term"] ↦ t ∗ m.[member, go!"vote"] ↦ vo ∗ m.[member, go!"commit"] ↦ cm ∗
      m.[member, go!"last"] ↦ l ∗ m.[member, go!"r"] ↦ r ∗ r ↦ rv }}
    (App (Val (m @!! go.GoType.PointerType member.ty @!! go!"opCommit")) (Val #()))
  {{ (b : Bool), RET #b;
      m.[member, go!"term"] ↦ t ∗ m.[member, go!"vote"] ↦ vo ∗ m.[member, go!"last"] ↦ l ∗
      m.[member, go!"r"] ↦ r ∗ (∃ rv' : rnd, r ↦ rv') ∗
      ((⌜b = true ∧ uint.nat l ≤ uint.nat cm⌝ ∗ m.[member, go!"commit"] ↦ cm ∗
          memSaveRes W e γ m w v o os c d qc) ∨
        (∃ cm' : w64, ⌜uint.nat cm < uint.nat cm' ∧ uint.nat cm' ≤ uint.nat l⌝ ∗
          m.[member, go!"commit"] ↦ cm' ∗
          memSavePost W e γ m w o c qc (hardState.mk t vo cm') [] b)) }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
