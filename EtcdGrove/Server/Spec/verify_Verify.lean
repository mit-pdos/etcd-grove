/-
`verify.Verify(msg, f)`, of etcd's `client/pkg/v3/verify` (translated names-only: it reads
the environment variable `ETCD_VERIFY` through `os.Getenv`). The trust boundary.
Lean-first (no Rocq counterpart); see `InvCindex.lean`.
-/
import EtcdGrove.Server.Base

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.client.pkg.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.pkg.v3.verify.Assumptions]

/-- `Verify(msg, f)`: if `ETCD_VERIFY` enables assertions, runs `f` and panics unless its
condition is `true`; otherwise does nothing. So the caller must show that `f` (if run, with
the caller's `P`) returns `true`: Go's code says "the check passes", and the spec rules the
panic out rather than assuming assertions are off. -/
abbrev verify.Verify.spec : Prop :=
  ∀ (msg : GoString) (f : val) (P : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.verify ∗ P ∗
      (P -∗ WP (App (Val f) (Val #())) {{ r, ∃ d : val, ⌜r = PairV #true d⌝ ∗ P }}) }}
    (App (App (Val (@! verify.Verify)) (Val #msg)) (Val f))
  {{ RET #(); P }}

end spec

end EtcdGrove
end Perennial
