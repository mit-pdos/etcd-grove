/- Lean-first (no Rocq counterpart).

`x.gen(l)` (`examples/mvccfull/mvccfull.go`): the log's next operation, made for the leader at
the model `s` (its `rev`, `cmp` and live leases' fields), every choice drawn: a put (a key, a new
value, `genLease`), a range delete, a transaction (`genSubs`, or one to three ranges), a grant of the
next id (`x.nextLease` incremented), a revoke of a live lease (a commit if none), a compaction (any
revision from `1` to one past the current one, one above the compaction revision, or the current
one; waiting or not), a commit, a read, or the lessor's check. The op is written once and returned
persistently (`opIs`), **valid at `s`** (`opValid`: the grant's id above every id granted, given
`nextLease` at least them). At most three values drawn (`vals`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Writer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- See the file header. -/
abbrev runner.gen.spec : Prop :=
  ∀ (x : Loc) (ks : List GoString) (cfg : Config) (wr : List w64) (h : Loc) (γh : HistNames)
    (mp : Loc) (s : MSt) (sl : GoSlice) (nl nv : w64),
  0 ≤ sint.Z nl → sint.Z nl + 1 < 2 ^ 63 → (∀ id ∈ s.granted, sint.Z id ≤ sint.Z nl) →
  0 ≤ sint.Z nv → sint.Z nv + 3 < 2 ^ 63 → s.rev + 2 < 2 ^ 63 → -1 ≤ s.crev → s.crev ≤ s.rev →
  {{ writerCtx (GF := GF) x ks cfg wr h γh ∗ mF go!"rev" mp ↦ (W64 (s.rev : Int)) ∗ mF go!"cmp" mp ↦ (W64 s.crev) ∗
      mF go!"leases" mp ↦ sl ∗ sl ↦* s.leases ∗ rF go!"nextLease" x ↦ nl ∗ rF go!"vals" x ↦ nv }}
    (App (x @!! go.GoType.PointerType runner.ty @!! go!"gen") (Val #mp))
  {{ (p : Loc), RET #p; mF go!"rev" mp ↦ (W64 (s.rev : Int)) ∗ mF go!"cmp" mp ↦ (W64 s.crev) ∗
      mF go!"leases" mp ↦ sl ∗ sl ↦* s.leases ∗
      ∃ (o : OpM) (nl' nv' : w64), opIs p o ∗ rF go!"nextLease" x ↦ nl' ∗ rF go!"vals" x ↦ nv' ∗
        ⌜opValid ks s o ∧ (nl' = nl ∨ (o.kind = kGrant ∧ o.id = nl + W64 1 ∧ nl' = nl + W64 1)) ∧
          sint.Z nv ≤ sint.Z nv' ∧ sint.Z nv' ≤ sint.Z nv + 3⌝ }}

end spec

end mvccfull
end EtcdGrove
end Perennial
