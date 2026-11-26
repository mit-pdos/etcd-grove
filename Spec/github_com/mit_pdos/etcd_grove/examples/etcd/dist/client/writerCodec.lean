/- Lean-first (no Rocq counterpart).

`writerCodec()` (`examples/etcd/dist/client/nodes.go`): **the watch writers' codec** (#50 N10a,
`notes/etcd-dist-plan.md` §24.6; the draft of `notes/remote-wire/WriterCodec.lean`, adopted): its four
functions are the writer's wire (`writerWire`, `WriterWire.lean`): `EncIn` of a `[]KV` describing
`(n, ps)` returns `kvsBytes ps`, `DecIn` of those bytes returns a fresh `[]KV` holding `ps` (read-only
once returned), likewise `EncOut`/`DecOut` for a `[]PutRec` log; a decoder may refuse. For any report
precondition `P` and postcondition `Q` (the service's update is not the codec's concern).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.WriterWire
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client go_etcd_io.etcd.server.v3.etcdserver
open etcd_dist etcdstart
open github_com.mit_pdos.etcd_grove.examples.lib.remote

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]

/-- See the file header. -/
abbrev writerCodec.spec : Prop :=
  ∀ (N : Type) (P : N × List wkv → IProp GF) (Q : N × List wkv → List wrec → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.writerCodec)) (Val #()))
  {{ (cd : github_com.mit_pdos.etcd_grove.examples.lib.remote.Codec), RET #cd;
      wireOk (reportSvc (writerWire (GF := GF) N) P Q) cd }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
