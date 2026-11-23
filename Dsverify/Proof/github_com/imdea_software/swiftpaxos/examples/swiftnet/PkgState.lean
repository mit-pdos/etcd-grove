/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/PkgState.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The run's choice of each package's package-level state (`SwiftNetPkgState`): what each package's
initialization establishes and its functions use (a global's points-to under an invariant, a
registration). Each package's prover owns its field and its body: the bodies here are the
current choices.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Pkg
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Pkg

open Perennial.Dsv

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- The packages' states. Status: `gob` is the gob model's (`Proof/gob/Base.lean`, owned by the
codec group); `swift`, `concurrent_map`, `replica`, `defs` are the swift prover's
(`Proof/swift/Pkg.lean`, change log C2, C6, C10); `client` is L2's
node ghost and its claim invariant (`client.pkgSt`, `Proof/client/Pkg.lean`, group E); every other field `True` until its package's proof needs a fact
(changing one changes `ClientOk`'s statement through `S` only, not a hub's text). -/
def pkgStates [GoGlobalContext] : SwiftNetPkgStates := fun {_GF} [_] [_] =>
  { utils := iprop(True), treemap := iprop(True), concurrent_map := cmap.pkgSt,
    gob := encoding.gob.isInit, rpc := iprop(True), dlog := iprop(True), config := iprop(True),
    state := iprop(True), hook := iprop(True), defs := defs.pkgSt, replica := replica.pkgSt,
    client := client.pkgSt, swift := swift.pkgSt, master := iprop(True) }

end Perennial.github_com.imdea_software.swiftpaxos
