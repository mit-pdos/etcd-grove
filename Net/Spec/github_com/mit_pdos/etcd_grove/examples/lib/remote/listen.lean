/-
`listen(addr)`: `net.Listen` at `addr`, retried until it succeeds; the node's listener at `addr`
(`listen_au` from the address's protocols). Proved in `Net/Proof/.../lib/remote/listen.lean`.
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
variable [π : NetProtoGS] [ρ : RemoteGS]
variable {I O : Type} [Pos.Countable I] [Pos.Countable O]

/-- See the file header. -/
abbrev listen.spec : Prop :=
  ∀ (S : RSvc GF I O) (a : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote ∗ svcAddr (Gg := hG.goose_globalGS) S a }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.remote.listen)) (Val #a))
  {{ (li : GoInterface), RET #li; ∃ l, net.isListener li l ∗
      netLis (extLocalGS netExt (L := hG.goose_localGS)) l a true ∗
      netLisAt (extLocalGS netExt (L := hG.goose_localGS)) l a }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.remote
end Perennial
