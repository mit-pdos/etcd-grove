/-
`clientv3.cloneCompare` (`client/v3/compare.go`).

Users: `Cmp.Clone`, `FromCompare`.

Proof sketch: `proto.Clone` (protobuf's boundary, 2a: a deep copy, owned) and the type assertion to `*pb.Compare`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/cloneCompare.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

verify-round: the fresh `*pb.Compare` (its `protoRest` from `protoRest_zero` at `own 1`) is made read-only for `cmpAt` by `protoRest_persist` (A1-provability F6: the sketch had no law for it).

second pass: `proto.Clone` (3h's `Proto.Clone.spec`) gives the copy the original's wire view
(`Proto.norm c`), whose model is the same comparison under `endsOk` (3h's `holds_norm`): every
`cmpAt` comparison has a `nil` or non-empty end (`Cmp.WithRange` takes `e ≠ []`).

re-review NF2: true now that `compareOwn_unfold` carries `RangeEnd = nil ∨ non-empty` (`Wire.lean`):
the caller's raw `*pb.Compare` must meet it (`FromCompare`: a scope premise through `compareOwn`, as
the KV triples' `emptyEnd = false`), and `proto.Clone`'s copy (`Proto.norm c`) then holds the same
model (3h's `holds_norm` under `endsOk`).

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `cloneCompare(c)`: `nil`, or a fresh copy, owned. -/
def cloneCompare.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (m : Option EtcdModel.Compare),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ optOwn compareOwn p dq m }}
    (App (Val (@! go_etcd_io.etcd.client.v3.cloneCompare)) (Val #p))
  {{ (p' : Loc), RET #p'; optOwn compareOwn p dq m ∗ optOwn compareOwn p' (DFrac.own 1) m }}

end spec

end ClientV3
end EtcdGrove
end Perennial
