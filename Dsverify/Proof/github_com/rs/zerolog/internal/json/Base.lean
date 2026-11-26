/-
The package fact of zerolog's `internal/json` (the part's translation, with bodies; dsv-retire-3,
2026-11-26, mit-pdos/etcd-grove#49 step 3): the hook cell `JSONMarshalFunc` (`base.go`; no
initializer), which zerolog's `init` (`encoder_json.go`) sets, in an init-time invariant (`hookCell`,
`Proof/runtime/InitInv.lean`: a package fact is persistent, and the cell is written by another
package's initializer, which takes it out of the invariant by lending its package state,
`EtcdGrove.grpcInternal.wp_store_hook`), and `noEscapeTable` (`string.go`), read-only for good, at
the value its `init` computes (`AppendString` and `AppendBytes` index it by a byte: in bounds, so
its contents do not matter to a spec that does not describe the output).
-/
module

public import Dsverify.GeneratedProof.github_com.rs.zerolog.internal.json
public import Net.Proof.net.Base
public import Proof.runtime.InitInv

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.rs.zerolog.internal.json

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`internal/json`'s package fact**: the hook cell `JSONMarshalFunc` (a `func`) in its init-time
invariant, and `noEscapeTable`, read-only. -/
def jsonInit : IProp GF :=
  iprop(_root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.hookCell
    GoFunc (globalAddr JSONMarshalFunc) ∗
    ∃ a : GoArray Bool 256, globalAddr noEscapeTable ↦□ a)

instance jsonInit_persistent : Persistent (jsonInit (GF := GF)) := by
  unfold jsonInit
  unfold _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.hookCell
  infer_instance

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.rs.zerolog.internal.json :=
  define_is_pkg_init jsonInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.rs.zerolog.internal.json :=
  build_get_is_pkg_init_wf

end def_

end github_com.rs.zerolog.internal.json
end Perennial
