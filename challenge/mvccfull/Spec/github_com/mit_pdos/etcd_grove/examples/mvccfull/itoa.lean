/- Lean-first (no Rocq counterpart).

`itoa(n)` (`examples/mvccfull/mvccfull.go`): `n`'s decimal digits, for `n ≥ 0` (`itoaM`, as
`strconv.Itoa`).
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.mvccfull
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]

end spec

end mvccfull
end EtcdGrove
end Perennial
