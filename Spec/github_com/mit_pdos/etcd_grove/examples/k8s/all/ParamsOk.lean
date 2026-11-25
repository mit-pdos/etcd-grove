/-
`ParamsOk(k1, clients, ops, watchers, wops, k2)` (`examples/k8s/all/checked.go`; the pure-premises
plan's P5, 2026-11-24): whether `Main`'s parameters are in the ranges its proof covers, `paramsOk`.
Until then those ranges were premises of the closed theorem (`k8s_robust_single_process.spec`'s
`hk₁1 … hk₂`, `Hc0 … Hmul`); `MainChecked` now checks them and returns when they fail. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.all.mulBelow

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_all

open Iris Iris.BI

/-- **The parameters `Main`'s proof covers**: the member counts `1 ≤ k₁ ≤ 1000` and `1 ≤ k₂ ≤ 600`
(unsigned); the clients and watchers nonnegative and fewer than `2^31` together, their operation counts
nonnegative, and the total `clients·ops + watchers·wops` (exact) below `2^60` (signed `int`s). -/
def paramsOk (k₁ clients ops watchers wops k₂ : w64) : Prop :=
  1 ≤ uint.Z k₁ ∧ uint.Z k₁ ≤ 1000 ∧ 1 ≤ uint.Z k₂ ∧ uint.Z k₂ ≤ 600 ∧
  0 ≤ sint.Z clients ∧ 0 ≤ sint.Z watchers ∧ sint.Z clients + sint.Z watchers < 2 ^ 31 ∧
  0 ≤ sint.Z ops ∧ 0 ≤ sint.Z wops ∧
  sint.Z clients * sint.Z ops + sint.Z watchers * sint.Z wops < 2 ^ 60

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.all.Assumptions]

/-- `ParamsOk` returns whether `paramsOk` holds of its arguments. -/
abbrev ParamsOk.spec : Prop :=
  ∀ (k₁ clients ops watchers wops k₂ : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.all }}
    (App (App (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.k8s.all.ParamsOk))
      (Val #k₁)) (Val #clients)) (Val #ops)) (Val #watchers)) (Val #wops)) (Val #k₂))
  {{ (b : Bool), RET #b; ⌜b = true ↔ paramsOk k₁ clients ops watchers wops k₂⌝ }}

end spec

end k8s_all
end EtcdGrove
end Perennial
