/-
`ParamsOk(k1, clients, ops, nw, nops, cnw, cnops, k2, k3, k4, k5)` (`examples/etcd/all/checked.go`;
the pure-premises plan's P4, 2026-11-24): whether `Main`'s parameters are in the ranges its proof
covers, `paramsOk`. Until then those ranges were premises of the closed theorem
(`etcd_robust_single_process.spec`'s `hk₁1 … hk₅`, `Hc0 … Hcmul`); `MainChecked` now checks them and
returns when they fail. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.all.mulBelow

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_all

open Iris Iris.BI

/-- **The parameters `Main`'s proof covers**: the member counts `1 ≤ k₁ ≤ 1000`, `1 ≤ k₂, k₃, k₄ ≤ 300`,
`3 ≤ k₅ ≤ 300` (unsigned), and each workload's client count in `[0, 2^31)`, its per-client operation
count nonnegative, and their product below `2^60` (txnlinfaultsN's) or `2^62` (partition's watches,
cache's) (signed `int`s, the product exact). -/
def paramsOk (k₁ clients ops nw nops cnw cnops k₂ k₃ k₄ k₅ : w64) : Prop :=
  1 ≤ uint.Z k₁ ∧ uint.Z k₁ ≤ 1000 ∧
  0 ≤ sint.Z clients ∧ sint.Z clients < 2 ^ 31 ∧ 0 ≤ sint.Z ops ∧
    sint.Z clients * sint.Z ops < 2 ^ 60 ∧
  0 ≤ sint.Z nw ∧ sint.Z nw < 2 ^ 31 ∧ 0 ≤ sint.Z nops ∧ sint.Z nw * sint.Z nops < 2 ^ 62 ∧
  0 ≤ sint.Z cnw ∧ sint.Z cnw < 2 ^ 31 ∧ 0 ≤ sint.Z cnops ∧ sint.Z cnw * sint.Z cnops < 2 ^ 62 ∧
  1 ≤ uint.Z k₂ ∧ uint.Z k₂ ≤ 300 ∧ 1 ≤ uint.Z k₃ ∧ uint.Z k₃ ≤ 300 ∧
  1 ≤ uint.Z k₄ ∧ uint.Z k₄ ≤ 300 ∧ 3 ≤ uint.Z k₅ ∧ uint.Z k₅ ≤ 300

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.all.Assumptions]

/-- `ParamsOk` returns whether `paramsOk` holds of its arguments. -/
abbrev ParamsOk.spec : Prop :=
  ∀ (k₁ clients ops nw nops cnw cnops k₂ k₃ k₄ k₅ : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.all }}
    (App (App (App (App (App (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.all.ParamsOk))
      (Val #k₁)) (Val #clients)) (Val #ops)) (Val #nw)) (Val #nops)) (Val #cnw)) (Val #cnops))
      (Val #k₂)) (Val #k₃)) (Val #k₄)) (Val #k₅))
  {{ (b : Bool), RET #b; ⌜b = true ↔ paramsOk k₁ clients ops nw nops cnw cnops k₂ k₃ k₄ k₅⌝ }}

end spec

end etcd_all
end EtcdGrove
end Perennial
