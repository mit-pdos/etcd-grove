/-
Port of `election_proof/spec_extend.v` (feb5c73d4).
-/
import EtcdGrove.Raft.InvRaftPhys

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `extend(dst, vals)`: `dst ++ vals` in a slice allocated to exactly the needed length
(`util.go`, "allocates only once").

**Restricted to the allocating branch**: the premise says the concatenation does not
fit in `cap(dst)`, so the `append(dst, vals...)` in-place branch is dead. That branch
would write into `dst`'s spare capacity, which this triple does not own -- and must not:
the only caller, `raftLog.slice`, passes a slice the `Storage` lent it, and
`Storage.Entries`'s contract (`InvStorage.lean`) guarantees `cap = len` precisely so
that the branch is never taken. A triple for the in-place branch would need
`ownSliceCap dst`; widen this one when a caller has it, rather than adding a second.

Both inputs are only read and come back at their fractions; the result is fresh and
fully owned. -/
abbrev extend.spec : Prop :=
  ∀ (dst vals : GoSlice) (ds vs : List raftpb.Entry) (dq1 dq2 : DFrac),
  sint.Z dst.cap < (ds.length : Int) + (vs.length : Int) →
  (ds.length : Int) + (vs.length : Int) < 2^63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hdst" ∷ dst ↦*{dq1} ds ∗
      "Hvals" ∷ vals ↦*{dq2} vs }}
    (App (App (Val #(functions extend [])) (Val #dst)) (Val #vals))
  {{ (s : GoSlice), RET #s;
      s ↦* (ds ++ vs) ∗ ownSliceCap raftpb.Entry s (DFrac.own 1) ∗
      dst ↦*{dq1} ds ∗ vals ↦*{dq2} vs }}

end spec

end EtcdGrove
end Perennial
