/-
`verify.Verify(msg, f)`, of etcd's `client/pkg/v3/verify` (it reads the environment variable
`ETCD_VERIFY` through `os.Getenv`). Proof: `Proof/go_etcd_io/etcd/client/pkg/v3/verify/Verify.lean`
(2026-11-20; the trust boundary until then). Lean-first (no Rocq counterpart); see `InvCindex.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.client.pkg.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.verify.Assumptions]

/-- `Verify(msg, f)`: if `ETCD_VERIFY` enables assertions, runs `f` and panics unless its
condition is `true`; otherwise does nothing. So the caller must show that `f` (if run, with
the caller's `P`) returns `true`: Go's code says "the check passes", and the spec rules the
panic out rather than assuming assertions are off. `f` is a Go function value (`GoFunc`, as bbolt's
`common.Verify`; every caller passes a function literal): until 2026-11-20 it was any `val`, which
the body's `GoAlloc VerifyFunc.ty f` gives no semantics for, and its `details` any `val` (a panic
outcome among them, which `Verify` would then unwind with), where it is a map, a `Loc`
(`notes/specs-only/ledger.md`). -/
abbrev verify.Verify.spec : Prop :=
  ∀ (msg : GoString) (f : GoFunc) (P : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.verify ∗ P ∗
      (P -∗ WP (App (Val #f) (Val #())) {{ r, ∃ d : Loc, ⌜r = PairV #true #d⌝ ∗ P }}) }}
    (App (App (Val (@! verify.Verify)) (Val #msg)) (Val #f))
  {{ RET #(); P }}

end spec

end EtcdGrove
end Perennial
