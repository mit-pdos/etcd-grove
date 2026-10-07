/-
Port of election_proof/spec_entsSize.v (feb5c73d4).
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

/-- `entsSize(ents)`: the summed encoded size of the entries. The value is
unspecified, since `Entry.Size` (pointer receiver) is (`spec_Entry__Size.v`);
`raftLog.slice` only compares it against `maxSize` to decide whether to append the
unstable part of its result, and either answer is fine. -/
abbrev entsSize.spec : Prop :=
  ∀ (s : GoSlice) (es : List raftpb.Entry) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hs" ∷ s ↦*{dq} es }}
    (App (Val #(functions entsSize [])) (Val #s))
  {{ (n : w64), RET #n; s ↦*{dq} es }}

end spec

end EtcdGrove
end Perennial
