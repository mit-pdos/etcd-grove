/-
Package initialization of `go_etcd_io.etcd.api.v3.etcdserverpb`
(item 8, 2026-10-17): its facts and trust-boundary axioms; its `wp_initialize'` is in
`InitLinked.lean` (2026-11-19: the proof applies other packages' `wp_initialize'` and
functions' proofs, so it is a linking module, CLAUDE.md "Import tiers").

Its fact (`etcdserverpbInit`, `cache/v3/Base.lean`): the sort enumerations' name maps. Its
initializer allocates and sets the translated gRPC service descriptors (`KV_ServiceDesc`, ...:
`grpc.ServiceDesc` literals), initializes its imports and runs its other variables' untranslated
initializers (the generated protobuf descriptors and enum maps), which the trust-boundary axiom
`opaqueInitsOk` says run. (const-inits, 2026-11-19) The two sort enumerations' name maps the fact
reads (`RangeRequest_SortOrder_name`, `RangeRequest_SortTarget_name`: `map[int32]string` literals,
`rpc.pb.go`) are translated and set; until then the trust-boundary axioms `<X>_init`. (etcd-grove#39, 2026-11-23) And `AlarmType_name` (a `map[int32]string` literal),
which the fact holds read-only, `etcdserverpb.alarmTypeNames`: `AlarmType.String`'s trusted model reads
it.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Perennial.Proof.context.Link
public import Proof.go_etcd_io.etcd.api.v3.authpb.Init
public import Proof.go_etcd_io.etcd.api.v3.membershippb.Init
public import Proof.go_etcd_io.etcd.api.v3.mvccpb.Init
public import Proof.google_golang_org.grpc.Init
public import Proof.google_golang_org.protobuf.runtime.protoimpl.Init

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

/-- A small 64-bit literal's value as a signed natural (the descriptors' slice indices). -/
theorem EtcdGrove.sint_nat_ofNat64 (n : Nat) (h : n < 2 ^ 63) : sint.nat (BitVec.ofNat 64 n) = n := by
  simp [sint.nat, BitVec.toInt]; omega

end Perennial
