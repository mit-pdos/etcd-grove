/- Lean-first (no Rocq counterpart).

`x.genSubs(m)` (`examples/mvccfull/mvccfull.go`): a write transaction's one to three
sub-operations, as etcd's `checkIntervals` allows them (`subsOk` at the keys and the member's live
leases `L`: the puts' keys distinct, none in a delete's range), each a fresh value's put with a lease
`0` or live, a range delete, or a range read at the member's next revision. The slice and each
sub-operation are returned persistently (never written after); at most three values drawn.
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
abbrev runner.genSubs.spec : Prop :=
  ∀ (x : Loc) (ks : List GoString) (cfg : Config) (mp : Loc) (rv c : w64) (sl : GoSlice)
    (L : List w64) (nv : w64),
  0 ≤ sint.Z nv → sint.Z nv + 3 < 2 ^ 63 → sint.Z rv + 1 < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗ runnerKeys x ks ∗ runnerRangeMix x cfg ∗ mF go!"rev" mp ↦ rv ∗ mF go!"cmp" mp ↦ c ∗
      mF go!"leases" mp ↦ sl ∗ sl ↦* L ∗ rF go!"vals" x ↦ nv }}
    (App (x @!! go.GoType.PointerType runner.ty @!! go!"genSubs") (Val #mp))
  {{ (ss : GoSlice), RET #ss; mF go!"rev" mp ↦ rv ∗ mF go!"cmp" mp ↦ c ∗
      mF go!"leases" mp ↦ sl ∗ sl ↦* L ∗
      ∃ (svs : List subOp) (sms : List SubM) (nv' : w64), ss ↦*□ svs ∗
        ([∗list] y ∈ svs.zip sms, subIs y.1 y.2) ∗ rF go!"vals" x ↦ nv' ∗
        ⌜svs.length = sms.length ∧ 1 ≤ sms.length ∧ sms.length ≤ 3 ∧ subsOk ks L sms ∧
          sint.Z nv ≤ sint.Z nv' ∧ sint.Z nv' ≤ sint.Z nv + 3⌝ }}

end spec

end mvccfull
end EtcdGrove
end Perennial
