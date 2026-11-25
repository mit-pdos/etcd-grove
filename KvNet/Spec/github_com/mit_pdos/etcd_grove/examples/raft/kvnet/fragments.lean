/-
`fragments(from, to, boot, seq, body)` (`udptransport.go`): the fragments of the message
(`fragsOf`, `UdpWire.lean`), each a new slice; nil exactly when `fragsOf` is `[]` (an empty body,
or one needing more than `maxFragments`). `body` is only read.
(kvudp, 2026-11-24: `notes/kvudp-proof-plan.md`.)
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Base
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.UdpWire

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Net Udp go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]

/-- See the file header. -/
abbrev fragments.spec : Prop :=
  ∀ (src dst boot seq : w64) (body : GoSlice) (q : DFrac) (bs : List w8),
  bs.length < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗ body ↦*{q} bs }}
    (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvnet.fragments)) (Val #src)) (Val #dst)) (Val #boot)) (Val #seq)) (Val #body))
  {{ (ds : GoSlice), RET #ds; body ↦*{q} bs ∗
      ⌜(ds = slice.nil ↔ fragsOf src dst boot seq bs = [])⌝ ∗
      ∃ dsl : List GoSlice, ds ↦* dsl ∗ ⌜dsl.length = (fragsOf src dst boot seq bs).length⌝ ∗
        [∗list] i ↦ d ∈ dsl, ∃ x, ⌜(fragsOf src dst boot seq bs)[i]? = some x⌝ ∗ d ↦* x }}

end spec

end raft_kvnet
end EtcdGrove
end Perennial
