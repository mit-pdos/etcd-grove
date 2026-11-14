/-
`(*member).opResend()` (wal.go) over `fsExt` (W4c U5): nothing if the last index is at `maxIndex = 2^62` or
above, or if the first candidate's history (`c.h ++ since`, folded by `walFold`) holds no entry at
`last + 1`; else up to three of its entries from `last + 1` on (consecutive indices), re-sent byte for
byte: the term raised to theirs, `terms` recording theirs, the last index moved, then `save` of the
member's hard state with those entries (`memSavePost`). The entries are well formed (they are the
history's: `tCheckWf o`), so the member's fields keep `tMemFields`. The size premise is room for three
entries (`tOrRoom o 152`). Lean-first (no Rocq counterpart).
-/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.MemberInv

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
abbrev member.opResend.spec : Prop :=
  ∀ (W : WalGS GF) (e : TEnv) (γ : TGS) (m w : Loc) (v : oracle) (o os : TOracle) (c : TCand)
    (d : WalDur) (qc : Qp) (t vo cm l : w64) (tm : Loc) (M : GMap w64 w64),
  e.orFile.Ok → tMemOk o c d → tMemHs o d → tCheckWf o → tOrRoom o 152 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      memSaveRes W e γ m w v o os c d qc ∗
      m.[member, go!"term"] ↦ t ∗ m.[member, go!"vote"] ↦ vo ∗ m.[member, go!"commit"] ↦ cm ∗
      m.[member, go!"last"] ↦ l ∗ m.[member, go!"terms"] ↦ tm ∗ tm ↦$ M }}
    (App (Val (m @!! go.GoType.PointerType member.ty @!! go!"opResend")) (Val #()))
  {{ (b : Bool), RET #b;
      m.[member, go!"vote"] ↦ vo ∗ m.[member, go!"commit"] ↦ cm ∗ m.[member, go!"terms"] ↦ tm ∗
      ((⌜b = true⌝ ∗ m.[member, go!"term"] ↦ t ∗ m.[member, go!"last"] ↦ l ∗ tm ↦$ M ∗
          memSaveRes W e γ m w v o os c d qc) ∨
        (∃ (t' l' : w64) (es : List TEnt) (M' : GMap w64 w64),
          ⌜1 ≤ es.length ∧ es.length ≤ 3 ∧ (∀ x ∈ es, tEntWf x) ∧ (tMemFields t M → tMemFields t' M')⌝ ∗
          m.[member, go!"term"] ↦ t' ∗ m.[member, go!"last"] ↦ l' ∗ tm ↦$ M' ∗
          memSavePost W e γ m w o c qc (hardState.mk t' vo cm) es b)) }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
