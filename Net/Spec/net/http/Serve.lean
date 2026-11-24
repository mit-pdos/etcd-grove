/-
`http.Serve(l, nil)` on a listener serving net/rpc over HTTP (`Serve.spec_rpc`): it serves the
connections `l` accepts with `DefaultServeMux` (a `nil` handler) until `Accept` fails, then returns
its error; it never panics. What it needs: the listener `l` at `la` (`isListener`, `netLisOn`,
`lisInv`), whose every address speaks net/rpc behind the `CONNECT` handshake for `path`
(`rpcLisP W la (connectReq path) connectAns`); the mux routing the literal path `path` to an rpc
handler at every address `l` takes (`muxRpc dmux W A path`, `A a` the addresses `l` accepts,
`MuxDefs.lean`; from `HandleHTTP`); net/http's server variables (`httpSrvEnv`); and the machine's
thread bound (`threadBound GF ≤ 2 ^ 31`, net/rpc's server's wait group, which the handler runs).
The shared rpc-over-HTTP design (L2) and its amendment 4 (agreed with phase 7's S5): S5's one
`Serve.spec`, over both an HTTP address and an rpc address, will imply it. Lean-first.
-/
module

public import Net.Proof.net.http.MuxDefs
public import Net.Proof.net.http.PkgInit
public import Net.Proof.net.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace net.http

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : net.http.Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS]

/-- See the file header. -/
abbrev Serve.spec_rpc : Prop :=
  ∀ (W : net.rpc.RpcWorld GF) (la path : GoString) (lis : GoInterface) (l : w64),
    litPattern path →
  {{ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ httpSrvEnv ∗
      net.rpc.rpcLisP (Gg := hG.goose_globalGS) W la (net.rpc.connectReq path) net.rpc.connectAns ∗
      muxRpc dmux W (fun a => addrOk a = true ∧ lisAccepts la a) path ∗
      net.isListener (GF := GF) lis l ∗ netLisOn (extLocalGS netExt (L := hG.goose_localGS)) l la ∗
      lisInv (Gg := hG.goose_globalGS) (extLocalGS netExt (L := hG.goose_localGS)) l la }}
    (App (App (Val (@! net.http.Serve)) (Val #lis)) (Val #(interface.nil : GoInterface)))
  {{ (err : GoInterface), RET #err; True }}

end spec
end net.http
end Perennial
