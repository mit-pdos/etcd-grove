/-
`Serve(addr, sys, op, codec, d)`: the node at `addr` (`remoteAddr`) that serves calls with `op`
over `sys` (`opMaybe`, its resource `tok sys`): it listens (`listen`) and serves the connections
one at a time (`serveConn`). It never returns. Proved in `Net/Proof/.../lib/remote/Serve.lean`.
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
variable {St I O : Type} [Pos.Countable I] [Pos.Countable O]

/-- See the file header. -/
abbrev Serve.spec : Prop :=
  ∀ (R : RBase GF St I O) (a : GoString) (sys : GoInterface) (op : GoFunc) (cd : remote.Codec)
    (d : w64) (tok : GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote ∗ remoteAddr (Gg := hG.goose_globalGS) R a ∗ codecOk R cd ∗ opMaybe R tok op ∗
      tok sys }}
    (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.remote.Serve)) (Val #a)) (Val #sys)) (Val #op)) (Val #cd))
      (Val #d))
  {{ RET #(); False }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
