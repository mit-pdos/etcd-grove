/- Lean-first (no Rocq counterpart).

`Codec()` (`examples/etcd/dist/kvremote`): txnlin's codec, a `remote.Codec` of seven function
literals, which computes the encodings and decodings of the far side's store `kvR γk` (`codecOk`,
`remote/Defs.lean`), for every `γk` (the codec does not look at the store's state): an input `boxIn x`
is `EncInput`'s bytes (`inputBytes x`), an output `boxOut y` `EncOutput`'s (`outputBytes y`); `IsRead`
is `!IsWrite`, which is the model input's `!isWrite`; `Unknown` is `Output{Err: true}` (`errOut`),
`IsUnknown` the field `Err`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Store

@[expose] public section

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.lib.remote
open EtcdGrove EtcdGrove.etcd_txnlin
open go_etcd_io.etcd.server.v3.etcdserver mvcc
open github_com.mit_pdos.etcd_grove.examples.lib

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Assumptions]

/-- See the file header. -/
abbrev Codec.spec : Prop :=
  ∀ γk : KVNames,
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Codec)) (Val #()))
  {{ (cd : remote.Codec), RET #cd; codecOk (kvR (GF := GF) γk) cd }}

end spec

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
end Perennial
