/-
`ParamsOk(k5)` (`examples/etcd/all/checked.go`; the pure-premises plan's P4, 2026-11-24): whether
`Main`'s parameter is in the range its proof covers, `paramsOk`. Until then that range was a premise of
the closed theorem (`etcd_restart_robust_single_process.spec`'s `hk₅`); `MainChecked` now checks it and returns
when it fails. Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_all

open Iris Iris.BI

/-- **The parameter `Main`'s proof covers**: restartN's member count `3 ≤ k₅ ≤ 300` (unsigned). -/
def paramsOk (k₅ : w64) : Prop :=
  3 ≤ uint.Z k₅ ∧ uint.Z k₅ ≤ 300

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.all.Assumptions]

/-- `ParamsOk` returns whether `paramsOk` holds of its argument. -/
abbrev ParamsOk.spec : Prop :=
  ∀ (k₅ : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.all }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.all.ParamsOk)) (Val #k₅))
  {{ (b : Bool), RET #b; ⌜b = true ↔ paramsOk k₅⌝ }}

end spec

end etcd_all
end EtcdGrove
end Perennial
