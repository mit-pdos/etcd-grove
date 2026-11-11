/- Lean-first (no Rocq counterpart).

`itoa(n)` (`examples/mvccrand/mvccrand.go`): `n`'s decimal digits, for `n ≥ 0` (`itoaM`, as
`strconv.Itoa`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccrand

/-- The decimal digits of `n` (none for `0`). -/
def decDigits (n : Nat) : GoString :=
  if _h : n = 0 then [] else decDigits (n / 10) ++ [W8 (48 + n % 10 : Nat)]
termination_by n
decreasing_by omega

/-- `n` in decimal (`"0"` for `0`). -/
def itoaM (n : Nat) : GoString := if n = 0 then go!"0" else decDigits n

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

/-- See the file header. -/
abbrev itoa.spec : Prop :=
  ∀ (n : w64), 0 ≤ sint.Z n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccrand.itoa)) (Val #n))
  {{ RET #(itoaM (sint.nat n)); True }}

end spec

end mvccrand
end EtcdGrove
end Perennial
