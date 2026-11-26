/-
The package fact of grpc's `internal` (the part's translation, `Dsverify/Code/google_golang_org/grpc/
internal.toml`; dsv-retire-2, 2026-11-25, mit-pdos/etcd-grove#49 step 2): the hook cell
`CanonicalString` (`internal.go`; no initializer), which `codes`' `init` sets and no translated code
reads, in an init-time invariant (`hookCell`, `Proof/runtime/InitInv.lean`, shared with the main
tree's grpc `internal`): a package fact is persistent, and the cell is another package's, so
`internal`'s initializer puts it in the invariant and `codes`' initializer, holding its package
state, takes it out for a plain store (`EtcdGrove.grpcInternal.wp_store_hook`).
-/
module

public import Dsverify.GeneratedProof.google_golang_org.grpc.internal
public import Net.Proof.net.Base
public import Perennial.Proof.time
public import Proof.runtime.InitInv

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace google_golang_org.grpc.internal

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`internal`'s package fact**: the hook cell `CanonicalString` (an `any`), in its init-time
invariant. -/
def internalInit : IProp GF :=
  _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.hookCell
    GoInterface (globalAddr CanonicalString)

instance internalInit_persistent : Persistent (internalInit (GF := GF)) := by
  unfold internalInit
  unfold _root_.Perennial.go_etcd_io.etcd.cache.v3.google_golang_org.grpc.internal.hookCell
  infer_instance

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.internal :=
  define_is_pkg_init internalInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.internal :=
  build_get_is_pkg_init_wf

end def_

end google_golang_org.grpc.internal
end Perennial
