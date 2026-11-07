/-
mvcc's randomized tester's results (`examples/mvccrand/mvccrand.go`, `notes/mvccrand.md`), restated,
with the trust base of each printed in the build log (`#print axioms`). Lean-first (no Rocq
counterpart).

* **`mvccrand_runChecks`** (`Link.lean`'s `mvccrand.wp_runChecks`): `runChecks(cfg)` -- a backend
  in a fresh file, the lessor and the store over it as etcd's server makes them, the post-lock
  hook, then the writer (`cfg.Ops` random puts, deletes, transactions, lease grants and revokes,
  reads), `cfg.Readers` readers and a watch stream's registrar and receiver run concurrently, every
  result of mvcc checked against the tester's model (a check that fails panics) -- returns the
  report, the lessor and the backend, or panics in `backend.New` (bbolt's open failing); so every
  check passes. From the package's `isPkgInit`, the main thread's token, the file's emptiness,
  `keySized`, the configuration's bounds and `ckptEffectsOk`
  (`Spec/github_com/mit_pdos/etcd_grove/examples/mvccrand/runChecks.lean`), and the hypothesis
  `sort.Slice.spec` (`Spec/sort/Slice.lean`: specified, neither proved nor assumed).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section results
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **Every check of mvcc's randomized tester passes** (`Link.lean`'s `mvccrand.wp_runChecks`; see
the file header), given `sort.Slice`'s spec. -/
theorem mvccrand_runChecks [go_etcd_io.etcd.cache.v3.Assumptions]
    (h_sort_Slice : sort.Slice.spec (GF := GF) (hG := hG)) :
    mvccrand.runChecks.spec (GF := GF) (hG := hG) :=
  mvccrand.wp_runChecks h_sort_Slice

end results

#print axioms mvccrand_runChecks

end EtcdGrove
end Perennial
