/-
`serveConn(c, sys, op, codec, d)` on the acceptor's end of a connection `cn` it accepted
(`accept_au`: its tokens and its fresh token): reads the request whole (`req_read`: the frame of
the input of the connection's slot), decodes it, claims the slot's update and the call's unit (`slot_claim`:
the fresh token, so at most once) and runs `op` with them (`svcOp`); records an answered output in
the slot (`slot_done`) and replies with the output's frame (`repP`), then closes. A request that
does not arrive whole, or does not decode, is not run. Proved in
`Net/Proof/.../lib/remote/serveConn.lean`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Defs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : github_com.mit_pdos.etcd_grove.examples.lib.remote.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]
variable {I O : Type} [Pos.Countable I] [Pos.Countable O]

/-- See the file header. -/
abbrev serveConn.spec : Prop :=
  ∀ (S : RSvc GF I O) (c : GoInterface) (cn : Nat) (a : GoString) (sys : GoInterface)
    (op : GoFunc) (cd : remote.Codec) (d : w64) (tok : GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote ∗ net.isConn (GF := GF) c cn true a ∗
      connEnd (Gg := hG.goose_globalGS) cn true (repP (Gg := hG.goose_globalGS) S) (reqP (Gg := hG.goose_globalGS) S a) [] [] ∗ connFresh (Gg := hG.goose_globalGS) cn true ∗
      wireOk S cd ∗ svcOp S a tok op ∗ tok sys }}
    (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.remote.serveConn)) (Val #c)) (Val #sys)) (Val #op)) (Val #cd))
      (Val #d))
  {{ RET #(); tok sys }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
