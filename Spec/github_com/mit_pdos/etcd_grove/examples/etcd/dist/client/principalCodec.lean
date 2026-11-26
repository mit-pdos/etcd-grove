/- Lean-first (no Rocq counterpart).

`principalCodec()` (`examples/etcd/dist/client/nodes.go`): **the auth principals' codec** (#50 F7 S7; the
pattern of `writerCodec`): its four functions are the principals' wire (`principalWire`, `PrincipalWire.lean`):
`EncIn` of a `string` describing `w` returns `encStr w`, `DecIn` of those bytes returns `w`, `EncOut`/`DecOut`
likewise for a `bool` (`encBool`); a decoder may refuse. For any report precondition `P` and postcondition `Q`
(the service's update is not the codec's concern).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.PrincipalWire
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client go_etcd_io.etcd.server.v3.etcdserver
open etcd_dist
open github_com.mit_pdos.etcd_grove.examples.lib.remote

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]

/-- See the file header. -/
abbrev principalCodec.spec : Prop :=
  ∀ (P : GoString → IProp GF) (Q : GoString → Bool → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.principalCodec)) (Val #()))
  {{ (cd : github_com.mit_pdos.etcd_grove.examples.lib.remote.Codec), RET #cd;
      wireOk (reportSvc (principalWire (GF := GF)) P Q) cd }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
