/-
mvcc's randomized tester's results (`examples/mvccrand/mvccrand.go`, `notes/mvccrand.md`), restated,
with the trust base of each printed in the build log (`#print axioms`). Lean-first (no Rocq
counterpart).

* **`mvccrand_Main`** (`Link.lean`'s `mvccrand.wp_Main`): `Main()` -- `Run` at seed 1 (1000 writer
  operations, 4 readers, 8 watchers): a backend in the fresh file `mvccrand.db`, the lessor and the
  store over it as etcd's server makes them, the post-lock hook, then the writer (random puts,
  deletes, transactions, lease grants and revokes, reads), the readers and a watch stream's
  registrar and receiver run concurrently, every result of mvcc checked against the tester's model
  (a check that fails panics), then the store, the lessor and the backend closed -- returns; so
  every check passes. From the package's `isPkgInit`, the file's emptiness, the thread
  and receipt bounds, `ckptEffectsOk`, `dbOpenOk` and `dbCloseOk` (bbolt's `Open` and `Close`
  succeeding; 2026-11-08: until then `runChecks`' result, which admitted `backend.New`'s panic)
  (`Spec/github_com/mit_pdos/etcd_grove/examples/mvccrand/Main.lean`), and the hypothesis
  `sort.Slice.spec` (`Spec/sort/Slice.lean`: specified, neither proved nor assumed). The closed
  theorem over it is `Adequacy.lean`'s `mvccrand_adequate`.
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

/-- **Every check of mvcc's randomized tester passes** (`Link.lean`'s `mvccrand.wp_Main`; see the
file header), given `sort.Slice`'s spec. -/
theorem mvccrand_Main [go_etcd_io.etcd.cache.v3.Assumptions]
    (h_sort_Slice : sort.Slice.spec (GF := GF) (hG := hG)) :
    mvccrand.Main.spec (GF := GF) (hG := hG) :=
  mvccrand.wp_Main h_sort_Slice

end results

#print axioms mvccrand_Main

end EtcdGrove
end Perennial
