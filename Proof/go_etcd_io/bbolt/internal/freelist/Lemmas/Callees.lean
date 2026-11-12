/-
Specs of callees that have none yet, which U2's proofs take as hypotheses (`notes/bbolt-proof-plan.md`,
design §5 item 4: "The `common.Verify` closures"):

- `common.Verify(f)` (internal/common, U1's package; the plan leaves it unstated): it runs `f`
  or not, depending on the environment (`getEnvVerify` reads `os.Getenv`).

`sort.SliceIsSorted` and `reflect.DeepEqual` (names-only: reflection), once stated here, are
trust-boundary specs now (`Spec/sort/SliceIsSorted.lean`, `Spec/reflect/DeepEqual.lean`), which this
module re-exports.
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas.Own
public import Spec.go_etcd_io.bbolt.internal.common.Verify
public import Spec.sort.SliceIsSorted
public import Spec.reflect.DeepEqual

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.freelist

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

-- `common.Verify`'s spec is `Spec/go_etcd_io/bbolt/internal/common/Verify.lean` (shared).

end spec

end bbolt
end EtcdGrove
end Perennial
