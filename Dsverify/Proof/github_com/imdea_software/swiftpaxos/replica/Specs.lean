/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/Specs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The replica group's internal specs (`replica/replica.go`, `replica/defs`), one triple each.

* `LatencyTable.WaitDurationID` on the deployment's nil table: zero.
* `ReplyBeacon(g)`: answers peer `g.Rid`'s beacon (a `GENERIC_SMR_BEACON_REPLY` frame on its
  writer, under `r.M`).
* `replicaListener(rid, br)`: reads peer `rid`'s stream to its end; every message of the
  table's types is decoded and handed, with its witness (`msgOk`), to the type's channel; never
  panics on any bytes the protocol (`inP`/`outQ`) admits, a stream cut short included.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.defs.Unmarshal

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]

/-- `(*LatencyTable)(nil).WaitDurationID(id)`: no latency table, no delay. -/
abbrev replica.defs.LatencyTable.WaitDurationID.spec : Prop :=
  ∀ (id : w64),
  {{ (True : IProp netDistGF) }}
    (App (Val (null @!! go.GoType.PointerType replica.defs.LatencyTable.ty @!!
      go!"WaitDurationID")) (Val #id))
  {{ RET #(W64 0); True }}

/-- `r.ReplyBeacon(g)`: answers peer `g.Rid`'s beacon. -/
abbrev replica.Replica.ReplyBeacon.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32) (g : Loc) (rid : w32)
    (ts : w64),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      replica.isReplica r γ γc γm γw N me ∗ g ↦ replica.defs.GBeacon.mk rid ts ∗
      ⌜0 ≤ rid.toInt ∧ rid.toInt < N⌝ }}
    (App (Val (r @!! go.GoType.PointerType replica.Replica.ty @!! go!"ReplyBeacon")) (Val #g))
  {{ RET #(); True }}

/-- `r.replicaListener(rid, br)` on peer `rid`'s reader `br` over end `k.side` of `cid`, which
has read the frames of `done` (`k`: the accepted connection after the peer's hello, or the
dialed one), with the listener's `Ewma[rid]`. -/
abbrev replica.Replica.replicaListener.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32) (rid : w64) (br : Loc)
    (k : sp.RdKind) (cv : GoInterface) (cid : w64) (R : List w8) (done : List sp.Msg)
    (ewsl : GoSlice) (e : w64),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.bufio ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.net ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.io ∗
      replica.isReplica r γ γc γm γw N me ∗
      ⌜(∃ id, k = .peerIn id) ∨ k = .peerOut⌝ ∗ ⌜0 ≤ sint.Z rid ∧ sint.Z rid < N⌝ ∗
      net.rpc.connIface cv cid k.side ∗ sp.connKind γ cid k.conn ∗
      bufio.ownReader br cv (recvTok cid k.side (k.proto γ γc γm)) R ∗ ⌜sp.rdAt k done R⌝ ∗
      replica.fld r go!"Ewma" ↦□ ewsl ∗ ⌜sint.Z ewsl.len = N⌝ ∗
      typedPointsto (sliceIndexRef w64 (sint.Z rid) ewsl) e (DFrac.own 1) }}
    (App (App (Val (r @!! go.GoType.PointerType replica.Replica.ty @!! go!"replicaListener"))
      (Val #rid)) (Val #br))
  {{ RET #(); True }}

end specs

end Perennial.github_com.imdea_software.swiftpaxos
