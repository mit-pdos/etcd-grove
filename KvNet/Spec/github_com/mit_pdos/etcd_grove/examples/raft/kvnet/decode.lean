/-
`decode(b)` (`examples/raft/kvnet/codec.go`): reads an operation's encoding back; `b` only read.
(kvdurable's `decode` is the same Go text, with the exact results, `decodeRet`; its spec names
kvreconf's `Base` for `decodeOp`, which the part cannot import: this weaker statement, all a caller
here needs, stands in until that spec imports kvreconf's `Pure` and the part reuses it.)
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.NodeDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Net go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev decode.spec : Prop :=
  ∀ (b : GoSlice) (d : List w8) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗ b ↦*{dq} d }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.decode)) (Val #b))
  {{ (i : w64) (k : w8) (key v : GoString) (ok : Bool),
      RET (PairV (PairV (PairV (PairV #i #k) #key) #v) #ok); b ↦*{dq} d }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
