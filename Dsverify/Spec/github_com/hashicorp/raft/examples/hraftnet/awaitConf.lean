/-
`hraftnet.awaitConf`'s spec (the hraft kit's configuration protocol, notes/dsv-hraft.md, S5d).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ConfDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.Assumptions]
variable [π : NetProtoGS]

open github_com.hashicorp.raft.examples.hraftnet

/-- `awaitConf(addr, ch)`: listens on `addr` (a failed `Listen` retried), accepts forever; a
connection's byte (`io.ReadFull`) is a prefix of the drawn size's (`confProto`), so the size; the
first is sent on `ch` (the future's `Fulfill`: `confOk γc`), each acknowledged, the connection
closed. It never returns. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.awaitConf.spec : Prop :=
  ∀ (γc : GName) (γf : FutureNames) (ch : Loc) (addr : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet ∗
        addrProto (Gg := hG.goose_globalGS) addr (confProto γc) ackProto ∗
        isFuture w64 γf ch ∗ Fulfill γf (confOk (G := hG.goose_globalGS) γc) }}
      (App (App (Val (@! awaitConf)) (Val #addr)) (Val #ch))
    {{ RET #(); True }}

end spec

end Perennial
