/-
**A one-member example's `premises`, from the interim bootstrap axiom** (2026-11-24; the linking module
of `BootOne.lean`, "Import tiers"): `premises_of_specOne` at `bootstrap.wp_proofOne`
(`Proof/.../etcdserver/bootstrapOne.lean`, interim, retired when #34 proves `bootstrap`). The one-member
examples' closed theorems take it in place of their named Iris premise (`Hprem`). Lean-first.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.BootOne
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.bootstrapOne

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section linked
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`premises` at Go's values** (see the file header): from the package's initialization, at the pure
facts `BootGo1` and the `fips140` setting off. -/
theorem premises_holds [ThreadBoundLe GF (2 ^ 29)] [ReceiptBoundLe GF (2 ^ 60)]
    (name peer client : GoString) (N : Nat) (id : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (hfips : crypto.fips140.GodebugFips140Off) (hf : BootGo1 name peer client id ctxs boot) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ⊢
      premises (GF := GF) name peer client N id ctxs boot :=
  premises_of_specOne (fun [_] => _root_.Perennial.EtcdGrove.bootstrap.wp_proofOne)
    name peer client N id ctxs boot hfips hf

end linked

end etcdstart
end EtcdGrove
end Perennial
