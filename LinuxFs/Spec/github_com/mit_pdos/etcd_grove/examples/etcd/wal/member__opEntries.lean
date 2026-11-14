/-
`(*member).opEntries()` (wal.go) over `fsExt` (W4c U5): nothing if the last index is at `maxIndex = 2^62` or
above; else one to four entries at the member's term `t` (indices from some `lo ≤ last + 1`, sizes from
`member.size`), recorded in `terms` (the indices above them deleted), the last index and possibly the
commit moved, then `save` of the member's hard state with those entries (`memSavePost`). The entries are
well formed (`tEntWf`: the term below `2^63` is the premise), and `terms` afterwards holds only `t` or
values it held (`tTermsFrom`). The stored oracles' size premise is room for the largest save
(`tOrRoom o 184`: four entries; `OrLen.lean`). Lean-first (no Rocq counterpart).
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
abbrev member.opEntries.spec : Prop :=
  ∀ (W : WalGS GF) (e : TEnv) (γ : TGS) (m w : Loc) (v : oracle) (o os : TOracle) (c : TCand)
    (d : WalDur) (qc : Qp) (t vo cm bs l : w64) (tm : Loc) (M : GMap w64 w64) (r : Loc) (rv : rnd),
  e.orFile.Ok → tMemOk o c d → tMemHs o d → uint.nat t < 2 ^ 63 → tOrRoom o 184 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗
      memSaveRes W e γ m w v o os c d qc ∗
      m.[member, go!"term"] ↦ t ∗ m.[member, go!"vote"] ↦ vo ∗ m.[member, go!"commit"] ↦ cm ∗
      m.[member, go!"base"] ↦ bs ∗ m.[member, go!"last"] ↦ l ∗ m.[member, go!"terms"] ↦ tm ∗
      tm ↦$ M ∗ m.[member, go!"r"] ↦ r ∗ r ↦ rv }}
    (App (Val (m @!! go.GoType.PointerType member.ty @!! go!"opEntries")) (Val #()))
  {{ (b : Bool), RET #b;
      m.[member, go!"term"] ↦ t ∗ m.[member, go!"vote"] ↦ vo ∗ m.[member, go!"base"] ↦ bs ∗
      m.[member, go!"terms"] ↦ tm ∗ m.[member, go!"r"] ↦ r ∗ (∃ rv' : rnd, r ↦ rv') ∗
      ((⌜b = true ∧ 2 ^ 62 ≤ uint.nat l⌝ ∗ m.[member, go!"commit"] ↦ cm ∗ m.[member, go!"last"] ↦ l ∗
          tm ↦$ M ∗ memSaveRes W e γ m w v o os c d qc) ∨
        (∃ (cm' l' : w64) (es : List TEnt) (M' : GMap w64 w64),
          ⌜1 ≤ es.length ∧ es.length ≤ 4 ∧ (∀ x ∈ es, tEntWf x ∧ x.term' = t) ∧ tTermsFrom t M M'⌝ ∗
          m.[member, go!"commit"] ↦ cm' ∗ m.[member, go!"last"] ↦ l' ∗ tm ↦$ M' ∗
          memSavePost W e γ m w o c qc (hardState.mk t vo cm') es b)) }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
