/-
`Then` and `Else` at plain operations (`notes/txn-nested.md`, S1′): the linked instances
(`v3.txn.wp_Then_plain`, `v3.txn.wp_Else_plain`) of the specs until the nested generalization
(`TxnPlainSpec.lean`'s `txn.Then.specPlain`, `txn.Else.specPlain`), for the linking modules whose
operations are all plain (a function's proof takes `txn.Then.spec` and applies `spec_plain`). No
`Link.lean` imports it, so the instances are not second proofs of `Then`/`Else`. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.Link
public import Proof.go_etcd_io.etcd.client.v3.TxnPlainSpec

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

namespace client

section links
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `Then`'s linked result at plain operations. -/
theorem v3.txn.wp_Then_plain : EtcdGrove.txn.Then.specPlain (GF := GF) (hG := hG) :=
  EtcdGrove.txn.Then.spec_plain v3.txn.wp_Then

/-- `Else`'s linked result at plain operations. -/
theorem v3.txn.wp_Else_plain : EtcdGrove.txn.Else.specPlain (GF := GF) (hG := hG) :=
  EtcdGrove.txn.Else.spec_plain v3.txn.wp_Else

end links

end client

end EtcdGrove
end Perennial
