/-
## `Verify(f)` (`internal/common/verify.go`)

**Users.** bucket.go:889 (`Bucket.free`'s check), bbolt's `tx.Commit` (`Check` under verification), freelist `Free`, `mergeSpans`, hashmap `FreeCount`: an optional self-check run when `BBOLT_VERIFY` asks for it. Snippet `ReqVerify`.
**Proof sketch.** `IsVerificationEnabled` reads `os.Getenv` and `strings.ToLower` (trusted: `req/os.md`, `req/strings.md`): either answer is possible, so both branches are proved: `f`'s WP, or nothing.
**Changes.** from `specs-ref`'s file of the same name (unchanged).
**Margin.** none: the post is what the code computes.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace BboltCommon

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

/-- `Verify(f)` runs `f` if the environment asks for it: `Q` must follow from `f` returning without a panic, and hold if it does not run. -/
def Verify.spec : Prop :=
  ∀ (f : GoFunc) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common ∗ (WP (App (Val #f) (Val #())) {{ fun v => iprop(⌜v.isPanic = false⌝ ∗ Q) }} ∧ Q) }}
    (App (Val (@! go_etcd_io.bbolt.internal.common.Verify)) (Val #f))
  {{ RET #(); Q }}

end spec

end BboltCommon
end EtcdGrove
end Perennial
