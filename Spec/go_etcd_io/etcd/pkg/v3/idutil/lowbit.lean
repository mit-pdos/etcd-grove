/-
## `idutil.lowbit(x, n)` (internal helper)

Users: `NewGenerator`, `Next`. Mirrors the code: `x & (MaxUint64 >> (64 - n))`. Changes: unchanged
in content. Margin: none (exact).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.idutil.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace IdUtil

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.idutil.Assumptions]

/-- `lowbit(x, n)` keeps the `n` low bits of `x` (`1 ≤ n ≤ 64`; Go's shift by `64 - n`). -/
def lowbit.spec : Prop :=
  ∀ (x : w64) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.idutil ∗
      ⌜1 ≤ uint.nat n ∧ uint.nat n ≤ 64⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.pkg.v3.idutil.lowbit)) (Val #x)) (Val #n))
  {{ RET #(x &&& (W64 (2 ^ 64 - 1) >>> (W64 64 - n))); True }}

end spec
end IdUtil
end EtcdGrove
end Perennial
