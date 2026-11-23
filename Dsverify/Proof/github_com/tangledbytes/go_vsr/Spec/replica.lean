/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Spec/replica.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; statements the lab's (the configured addresses
`VsrWire.addrs`; the JSON vocabulary `Spec/jsonlib.lean`'s, the logger `Spec/sloglib.lean`'s).
-/
/-
Cross-package specs of `pkg/replica` (called by the server node's program, `vsrnet.serve`): the
`*Replica` (`isReplica rp γ r tcp`, exclusive: owned by the node's event loop) of replica `r`
of the system `γ`, sending through the `*TCP` `tcp`. Specs: `New`, `Submit`, `Run`.

The replica's model state (`repOwn γ r _`), the system's invariants and its service (a handler
`srvOk h P` of a store resource `P`) are inside `isReplica`.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.network
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.time
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.vsrkv
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Inv

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : replica.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

/-- The `*Replica` `rp` is replica `r` of `γ` over the `*TCP` `tcp` (exclusive).
-- sealed: the package's choice -/
def replica.isReplica (rp : Loc) (γ : VsrGhost.Names) (r : Nat) (tcp : Loc) :
    IProp GF := replica.own rp γ r tcp

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : replica.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]
variable [models_lab.jsoncodec.JsonCodec GF]

set_option goose.wp.extras true

/-- `New(cfg)`: replica `cfg.ID` (`r < n`) of `n` configured members (any order; `n` the system's
number of replicas, `fact γ (.size n)`), serving through the handler `cfg.SrvHandler` (`srvOk`
of a resource `P`, given at the empty store), over the `*TCP` `tcp` (its sender right given), a
`*Real` time, a logger; replica `r`'s initial model state, the system's invariants, the
addresses' protocols, the JSON codec registered (scanner `F`). No error, and the replica. -/
abbrev replica.New.spec : Prop :=
  ∀ (F : List w8 → Bool → w64 × w64) (cfg : replica.Config) (γ : VsrGhost.Names) (n r : Nat)
    (tcp : Loc) (me : GoString) (dq : DFrac) (ms : List GoString)
    (P : VsrModel.Store → IProp GF),
  uint.nat cfg.ID' = r → r < n → ms.length = n → n < 2 ^ 62 → (∀ a ∈ ms, a ∈ VsrWire.addrs) →
  cfg.Network' = interface.mkOk (go.GoType.PointerType network.TCP.ty) #tcp →
  time.isTime cfg.Time' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
      cfg.Members' ↦*{dq} ms ∗ examples.vsrkv.srvOk cfg.SrvHandler' P ∗ P (fun _ => none) ∗
      network.isTCP tcp γ me ∗ network.tcpSender tcp ∗ network.netProtos γ ∗
      log.slog.isLogger cfg.Logger' ∗
      VsrGhost.repOwn γ r VsrModel.initRep ∗ VsrGhost.fact γ (.size n) ∗
      VsrGhost.sysInv γ ∗ VsrGhost.regInv γ ∗
      encoding.json.codecSet (GF := GF) ∗ encoding.json.kitCodecOk F }}
    (App (Val (@! replica.New)) (Val #cfg))
  {{ (rp : Loc), RET (PairV #rp #(interface.nil : GoInterface));
      cfg.Members' ↦*{dq} ms ∗ replica.isReplica rp γ r tcp }}

/-- `rp.Submit(ev)`, an event `tcp` received (with its payload's `Logs` capacity). -/
abbrev replica.Replica.Submit.spec : Prop :=
  ∀ (rp : Loc) (γ : VsrGhost.Names) (r : Nat) (tcp : Loc) (ev : events.NetworkEvent),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
      replica.isReplica rp γ r tcp ∗
      ∃ m : Msg, events.isEvent ev.Event' m ∗ VsrGhost.fact γ (.msg m) ∗
        network.addrOk tcp ev.Src' ∗ events.evCap ev.Event' m }}
    (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"Submit")) (Val #ev))
  {{ RET #(); replica.isReplica rp γ r tcp }}

/-- `rp.Run()`: one round of the event loop (one submitted event, the timers). -/
abbrev replica.Replica.Run.spec : Prop :=
  ∀ (rp : Loc) (γ : VsrGhost.Names) (r : Nat) (tcp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
      replica.isReplica rp γ r tcp }}
    (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"Run")) (Val #()))
  {{ RET #(); replica.isReplica rp γ r tcp }}

end spec

end Perennial.github_com.tangledbytes.go_vsr.pkg
