/-
`ServeClient(c, addr, newClient, op, codec, d)`: client node `c`'s program: its own client of
the system (`newClient(c)`, its resource `tok sys`), then `Serve`. It never returns. Proved in
`Net/Proof/.../lib/remote/ServeClient.lean`.
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
abbrev ServeClient.spec : Prop :=
  ∀ (S : RSvc GF I O) (c : w64) (a : GoString) (newClient op : GoFunc) (cd : remote.Codec)
    (d : w64) (tok : GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote ∗ svcAddr (Gg := hG.goose_globalGS) S a ∗ wireOk S cd ∗ svcOp S tok op ∗
      {{ True }} (App (Val #newClient) (Val #c)) {{ (sys : GoInterface), RET #sys; tok sys }} }}
    (App (App (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient)) (Val #c)) (Val #a)) (Val #newClient))
      (Val #op)) (Val #cd)) (Val #d))
  {{ RET #(); False }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
