/-
`types.NewURLs`: the trust boundary (`go.etcd.io/etcd/client/pkg/v3/types` is names-only; rafthttp
stage 6a, `Transport.AddPeer`/`AddRemote`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.client.pkg.v3.types.URLs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`types.NewURLs(strs)`** of a non-empty list of plain peer URL strings (`http://host:port`):
no error, and a new slice of as many URLs, each the parse of one of the strings
(`parsedPeerURL`: scheme `http`, its host, nothing else; sorted, so in some order). -/
abbrev types.NewURLs.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (ss : List GoString),
  ss ≠ [] → (∀ s ∈ ss, types.plainPeerURL s) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.types ∗ sl ↦*{dq} ss }}
    (App (Val (@! go_etcd_io.etcd.client.pkg.v3.types.NewURLs)) (Val #sl))
  {{ (us : GoSlice) (uvs : List _root_.Perennial.net.url.URL), RET (PairV #us #GoInterface.nil);
      sl ↦*{dq} ss ∗ us ↦* uvs ∗
      ⌜uvs.length = ss.length ∧ ∀ u ∈ uvs, ∃ s ∈ ss, types.parsedPeerURL s u⌝ }}

end spec

end EtcdGrove
end Perennial
