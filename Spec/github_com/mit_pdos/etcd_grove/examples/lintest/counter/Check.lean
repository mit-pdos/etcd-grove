/- Lean-first (no Rocq counterpart).

`Check(clock, clients, ops, timeout)` (counter.go): `lintest.Run` on a fresh counter, its
model and the generator `func(id int) any` (an `Inc` for an even client, a `Read` for an odd
one), with the given clock. For any clock with `clockSpec` (whose invariants are not
`lintestN`), under `Run`'s bounds on `clients` and `ops`, the result is never `Illegal`, and
it is `Ok` if `timeout ≤ 0`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.counter.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest
namespace counter

open Iris Iris.BI github_com.anishathalye.porcupine

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lintest.counter.Assumptions]

/-- See the file header. -/
abbrev Check.spec : Prop :=
  ∀ (clockVal : w64 → IProp GF) (t0 : w64) (Eclk : CoPset) (clock : GoFunc)
    (clients ops dur : w64),
  (↑lintestN : CoPset) ⊆ ⊤ \ Eclk →
  0 ≤ sint.Z clients → sint.Z clients < 2 ^ 31 → 0 ≤ sint.Z ops →
  sint.Z clients * sint.Z ops < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lintest.counter ∗
      clockSpec clockVal Eclk clock ∗ clockVal t0 }}
    (App (App (App (App
      (Val (@! github_com.mit_pdos.etcd_grove.examples.lintest.counter.Check))
      (Val #clock)) (Val #clients)) (Val #ops)) (Val #dur))
  {{ (r : GoString), RET #r; ⌜r ≠ go!"Illegal" ∧ (sint.Z dur ≤ 0 → r = go!"Ok")⌝ }}

end spec

end counter
end lintest
end EtcdGrove
end Perennial
