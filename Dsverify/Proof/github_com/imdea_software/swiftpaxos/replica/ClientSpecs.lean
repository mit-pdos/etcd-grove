/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/ClientSpecs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The client listener's specs (`replica/replica.go` `clientListener`) and its callees' (internal):

* `replica.defs.Propose.Unmarshal.spec`: without an error, the bytes read decode to a proposal
  (`sp.decodes (W8 0)`), which the struct then holds, its value a fresh slice.
* `LatencyTable.WaitDuration` on the nil table, `NewDelayProposeChan(0, c)` and its `Write`
  (a send on `c`), `ProxyInfo.IsProxy` on an empty `ProxyInfo`.
* `clientListener(conn, br, first, hasFirst)`: reads a connection accepted on the replica's port
  to its end (its first byte read here with `ReadByte`, or already by `waitForPeerConnections`:
  `hasFirst`, the R2 workaround); a peer's connection (P1: its first byte is the hello's) or one
  whose first read fails is closed; a client's proposals are
  each handed, owned and with their registration (`cmdIs`), to `ProposeChan`, the client's
  writer registered in `ClientWriters`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.Specs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

-- PORT: lab imports dropped: Harness.Proof.net.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section generic
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [replica.defs.Assumptions] [state.Assumptions] [sp.GobFmt]

/-- `(*Propose).Unmarshal(rd)`: see the file header. -/
abbrev replica.defs.Propose.Unmarshal.spec : Prop :=
  ∀ (t : Loc) (v : replica.defs.Propose) (rd : GoInterface) (I : List w8 → IProp GF)
    (R : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.io ∗ isPkgInit (PROP := IProp GF) pkg_id.encoding.binary ∗
      bufio.readsOk rd I ∗ I R ∗ t ↦ v }}
    (App (Val (t @!! go.GoType.PointerType replica.defs.Propose.ty @!! go!"Unmarshal")) (Val #rd))
  {{ (err : GoInterface), RET #err; ∃ data : List w8, I (R ++ data) ∗
      ((⌜err = interface.nil⌝ ∗ ∃ (seq cl : w32) (c : sp.Cmd) (ts : w64) (vs : GoSlice),
          ⌜sp.decodes (W8 0) data (.propose seq cl c ts)⌝ ∗
          t ↦ replica.defs.Propose.mk seq cl (state.Command.mk c.op c.key vs) ts ∗ vs ↦* c.val) ∨
        (⌜err ≠ interface.nil⌝ ∗ ∃ v' : replica.defs.Propose, t ↦ v')) }}

end generic

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions] [config.Assumptions]

/-- `(*LatencyTable)(nil).WaitDuration(addr)`: no delay. -/
abbrev replica.defs.LatencyTable.WaitDuration.spec : Prop :=
  ∀ (addr : GoString),
  {{ (True : IProp netDistGF) }}
    (App (Val (null @!! go.GoType.PointerType replica.defs.LatencyTable.ty @!!
      go!"WaitDuration")) (Val #addr))
  {{ RET #(W64 0); True }}

/-- A `*DelayProposeChan` without delay over `c` (persistent). -/
def replica.defs.dpcOk (dc : Loc) (c : GoChan) : IProp netDistGF :=
  iprop(∃ v : replica.defs.DelayProposeChan, dc ↦□ v ∗ ⌜v.delay' = W64 0 ∧ v.pChan' = c⌝)

instance replica.defs.dpcOk_persistent (dc : Loc) (c : GoChan) :
    Persistent (replica.defs.dpcOk dc c) := by
  unfold replica.defs.dpcOk; infer_instance

/-- `NewDelayProposeChan(0, c)`. -/
abbrev replica.defs.NewDelayProposeChan.spec : Prop :=
  ∀ (c : GoChan),
  {{ (True : IProp netDistGF) }}
    (App (App (Val (@! replica.defs.NewDelayProposeChan)) (Val #(W64 0))) (Val #c))
  {{ (dc : Loc), RET #dc; ∃ v : replica.defs.DelayProposeChan, dc ↦ v ∗
      ⌜v.delay' = W64 0 ∧ v.pChan' = c⌝ }}

/-- `dc.Write(p)` without delay: sends `p` on the bag channel `c`. -/
abbrev replica.defs.DelayProposeChan.Write.spec : Prop :=
  ∀ (dc : Loc) (c : GoChan) (γch : ChanNames) (P : Loc → IProp netDistGF) (p : Loc),
  {{ replica.defs.dpcOk dc c ∗ isChanBag γch c P ∗ P p }}
    (App (Val (dc @!! go.GoType.PointerType replica.defs.DelayProposeChan.ty @!! go!"Write"))
      (Val #p))
  {{ RET #(); True }}

/-- `pi.IsProxy(alias, addr)` on an empty `ProxyInfo`: false. -/
abbrev config.ProxyInfo.IsProxy.spec : Prop :=
  ∀ (pp : Loc) (pi : config.ProxyInfo) (al addr : GoString),
  {{ (pp ↦□ pi : IProp netDistGF) ∗ ⌜pi.proxies' = null⌝ }}
    (App (App (Val (pp @!! go.GoType.PointerType config.ProxyInfo.ty @!! go!"IsProxy"))
      (Val #al)) (Val #addr))
  {{ RET #false; True }}

/-- `r.clientListener(conn, br, first, hasFirst)` on a connection accepted on the replica's
port, nothing written yet, nothing read (`hasFirst` false) or only its first byte `first`, not
the peers' hello (`hasFirst` true: read by `waitForPeerConnections`; see the file header), with
the protocol fact of what was read (`protoPrefix`: the reader's comes a step later). -/
abbrev replica.Replica.clientListener.spec : Prop :=
  ∀ (r : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me : w32) (al : GoString)
    (cv : GoInterface) (cid : Nat) (br : Loc) (first : w8) (hasFirst : Bool),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.bufio ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.net ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.io ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.strings ∗
      replica.isReplica r γ γc γm γw N me ∗ replica.fld r go!"Alias" ↦□ al ∗
      net.rpc.connIface cv cid true ∗
      bufio.ownReader br cv (recvTokL cid true (sp.inP γ γc γm))
        (if hasFirst then [first] else []) ∗
      protoPrefix (sp.inP γ γc γm) cid (if hasFirst then [first] else []) ∗
      ⌜hasFirst = true → first ≠ W8 0xFF⌝ ∗
      sendTok cid true (sp.outQ γ γc γm) [] }}
    (App (App (App (App
      (Val (r @!! go.GoType.PointerType replica.Replica.ty @!! go!"clientListener"))
      (Val #cv)) (Val #br)) (Val #first)) (Val #hasFirst))
  {{ RET #(); True }}

end specs

end Perennial.github_com.imdea_software.swiftpaxos
