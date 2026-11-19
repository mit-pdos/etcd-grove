/-
Package initialization of `github_com.mit_pdos.etcd_grove.examples.k8s.etcd3`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`drvInit`, `Base.lean`): its error variables (`k8setcd3.go`: `errNotObj`,
`errBadData`, `errBadRV`, `errDeleteRejected`, `errUpdateRejected`, translated
`errors.New` calls) each hold a fixed `*errorString` whose `Error()` returns and whose cell holds
its message (`wp_New_errorString_cell`). Its initializer allocates them, initializes its imports
and runs their translated initializers.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Base
public import Perennial.Proof.context.Link
public import Perennial.Proof.errors.Link
public import Perennial.Proof.github_com.goose_lang.primitive.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.strings.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Proof.github_com.anishathalye.porcupine.Init
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Init
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Init
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.Init
public import Proof.github_com.mit_pdos.etcd_grove.third_party.bridge.Init
public import Proof.go_etcd_io.etcd.client.v3.Init
public import Proof.go_etcd_io.etcd.client.v3.kubernetes.Init
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Init
public import Proof.go_uber_org.zap.Init
public import Proof.k8s_io.apimachinery.pkg.apis.meta.v1.Init
public import Proof.k8s_io.apimachinery.pkg.fields.Init
public import Proof.k8s_io.apimachinery.pkg.labels.Init
public import Proof.k8s_io.apimachinery.pkg.runtime.Init
public import Proof.k8s_io.apimachinery.pkg.runtime.schema.Init
public import Proof.k8s_io.apimachinery.pkg.types.Init
public import Proof.k8s_io.apimachinery.pkg.watch.Init
public import Proof.k8s_io.apiserver.pkg.storage.Init
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Init
public import Proof.k8s_io.apiserver.pkg.storage.value.Init
public import Proof.k8s_io.apiserver.pkg.util.feature.Init
public import Proof.errors.NewVarCell

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

end Perennial
