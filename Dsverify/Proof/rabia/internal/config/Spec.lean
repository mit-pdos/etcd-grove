/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/config/Spec.lean`, run `rabia-r1wake-1`.)

`rabia/internal/config`'s specs used by other packages (interface, stage 1a).

`config.Conf` is written once per node, by the kit's `configure` (before any routine reads it),
then only read. `confVal cf ps` is the value `configure(ps, conf)` leaves (`kit.go`'s fields, then
`CalcConstants`); `confRO cf` says `Conf` holds it, read-only (persistent), for some peers slice
`ps` holding the servers' network addresses (stage 2: at the configuration `cf` the client node
chose). Every reader of `Conf` takes `confRO cf`.

`isPkgInit config` (the package state, `Proof/Rabia/PkgState.lean`) keeps `Conf`'s points-to from
the package's initialization (SF2: the client node's `New` claims it with its address's unset
protocol; a server keeps it from its boot).
-/
module

public import Dsverify.GeneratedProof.rabia.internal.config
public import Dsverify.Proof.rabia.Core.Model
public import Dsverify.Proof.rabia.Core.Proto
public import Dsverify.Proof.rabia.internal.config.Base



@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.config

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The servers' network addresses (`Conf.Peers`): the first `n` server nodes' (`peers`). -/
def peerStrs (cf : model.RCfg) : List GoString := (List.range cf.n).map netAddr

/-- `Conf` after the kit's `configure(ps, conf)` in configuration `cf` (`kit.go`'s fields, then
`CalcConstants`, then `LenBlockArray`). -/
def confVal (cf : model.RCfg) (ps : GoSlice) : Config :=
  { Role' := go!"svr", Id' := [], ControllerAddr' := [], ProjectFolder' := go!"/tmp/rabia-net",
    LogLevel' := go!"warn", SvrIp' := [], ProxyPort' := [], NetworkPort' := [], Peers' := ps,
    ProxyAddr' := [], ClosedLoop' := true, NServers' := W64 cf.n, NFaulty' := W64 cf.f,
    NClients' := W64 6, NConcurrency' := W64 1, NClientRequests' := W64 8,
    ClientThinkTime' := W64 0, ClientBatchSize' := W64 1, ProxyBatchSize' := W64 cf.batchSize,
    ProxyBatchTimeout' := W64 (cf.batchMs * 1000000), NetworkBatchSize' := W64 0,
    NetworkBatchTimeout' := W64 0, NMinusF' := W64 cf.q, Majority' := W64 cf.maj,
    MajorityPlusF' := W64 cf.mpf, FaultyPlusOne' := W64 cf.fp1, LenLedger' := W32 10000,
    LenBlockArray' := W64 cf.blockLen, LenChannel' := W64 500000, LenPQueue' := W64 0,
    IoBufSize' := W64 16384000, TcpBufSize' := W64 7000000, KeyLen' := W64 8,
    ValLen' := W64 8, SvrLogInterval' := W64 4000000000,
    ClientLogInterval' := W64 15000000000, ClientTimeout' := W64 0,
    ConsensusStartAfter' := W64 0, StorageMode' := W64 0, RedisAddr' := zeroValDef }

/-- `Conf` holds the deployment's configuration `cf`, read-only (persistent). -/
def confRO (cf : model.RCfg) : IProp GF :=
  iprop(⌜cf.Ok⌝ ∗ ∃ ps, (globalAddr Conf ↦□ confVal cf ps : IProp GF) ∗ ps ↦*□ peerStrs cf)

/-- The configuration's value (a law: clients do not unfold `confRO`). -/
theorem confRO_val (cf : model.RCfg) :
    confRO (GF := GF) cf ⊢ ∃ ps, (globalAddr Conf ↦□ confVal cf ps : IProp GF) := by
  unfold confRO; iintro ⟨-, %ps, #H, -⟩; iexists ps; iexact H

/-- The configuration is one `choose` can pick (H2-ledger-1). -/
theorem confRO_ok (cf : model.RCfg) : confRO (GF := GF) cf ⊢ ⌜cf.Ok⌝ := by
  unfold confRO; iintro ⟨%h, -⟩; ipureintro; exact h

instance confRO_persistent (cf : model.RCfg) : Persistent (confRO (GF := GF) cf) := by
  unfold confRO; infer_instance

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.config.Assumptions]

/-- `(*Config).CalcConstants()`: the derived constants (`n - f`, quorums, lengths, sizes,
intervals), from `NServers`, `NFaulty` and `NClientRequests`. -/
abbrev Config.CalcConstants.spec : Prop :=
  ∀ (c : Loc) (v : Config),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.config ∗ c ↦ v }}
    (App (Val (c @!! go.GoType.PointerType Config.ty @!! go!"CalcConstants")) (Val #()))
  {{ RET #(); c ↦ { v with
      NMinusF' := v.NServers' - v.NFaulty',
      Majority' := v.NServers'.sdiv (W64 2) + W64 1,
      MajorityPlusF' := v.NServers'.sdiv (W64 2) + v.NFaulty' + W64 1,
      FaultyPlusOne' := v.NFaulty' + W64 1,
      NClientRequests' := if v.NClientRequests' = W64 0 then W64 10000000 else v.NClientRequests',
      LenLedger' := W32 10000, LenBlockArray' := W64 10, LenChannel' := W64 500000,
      IoBufSize' := W64 16384000, TcpBufSize' := W64 7000000, KeyLen' := W64 8,
      ValLen' := W64 8, SvrLogInterval' := W64 4000000000,
      ClientLogInterval' := W64 15000000000, ConsensusStartAfter' := W64 0 } }}

end spec

end Perennial.rabia.internal.config
