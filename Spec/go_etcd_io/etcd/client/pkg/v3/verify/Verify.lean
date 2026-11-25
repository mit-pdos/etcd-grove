/-
`verify.Verify(msg, f)`, of etcd's `client/pkg/v3/verify` (it reads the environment variable
`ETCD_VERIFY` through `os.Getenv`). Proved (etcdstorage, 2026-11-20; until then the trust boundary).
Lean-first (no Rocq counterpart); see `InvCindex.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Base
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.Env

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
panic out rather than assuming assertions are off. (etcdstorage, 2026-11-20) Or that assertions
are off for the run (`EtcdVerifyOff`; until 2026-11-25 the token `envVerifyOff`), when `f` is not run: a weaker premise, for checks whose
condition no proof shows (`backend.VerifyBackendConsistency`'s). (etcdstorage, 2026-11-20) `f` is a
`GoFunc` (a typed value, never a panic value; until then any `val`, under which `Verify` with
assertions off would not return: the call's argument would panic first), and the details `f` returns
are a map (`d : Loc`, `map[string]any`'s values; until then any `val`, which `Verify` could not store
into its `map[string]any` variable). -/
abbrev verify.Verify.spec : Prop :=
  ∀ (msg : GoString) (f : GoFunc) (P : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.verify ∗ P ∗
      ((P -∗ WP (App (Val #f) (Val #())) {{ r, ∃ d : Loc, ⌜r = PairV #true #d⌝ ∗ P }}) ∨
        ⌜EtcdVerifyOff⌝) }}
    (App (App (Val (@! verify.Verify)) (Val #msg)) (Val #f))
  {{ RET #(); P }}

end spec

end EtcdGrove
end Perennial
