/- Lean-first (no Rocq counterpart).

`w.genLease()` (`examples/mvccrand/mvccrand.go`): no lease (`0`) half the time or when the model has
no live lease, else one of the model's live leases `Lm` (the ids sorted, one chosen at random). The
map is only read; the generator moves.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.Writer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- See the file header. -/
abbrev writer.genLease.spec : Prop :=
  ∀ (w : Loc) (wv : writer) (Lm : GMap w64 Bool) (g : rng),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand ∗
      writerRO w wv ∗ wv.leases' ↦$ Lm ∗ wv.r' ↦ g }}
    (App (Val (w @!! go.GoType.PointerType writer.ty @!! go!"genLease")) (Val #()))
  {{ (l : w64), RET #l; wv.leases' ↦$ Lm ∗ (∃ g' : rng, wv.r' ↦ g') ∗
      ⌜l = W64 0 ∨ (Lm !! l).isSome = true⌝ }}

end spec

end mvccrand
end EtcdGrove
end Perennial
