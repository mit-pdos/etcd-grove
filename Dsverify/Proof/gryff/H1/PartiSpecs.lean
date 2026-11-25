/-
The participant's methods' triples (`gryffcommon/participant.go`), as specs (CLAUDE.md, "Import
tiers": a proof sees its callees through their specs only). `GryffPartiDeps` bundles them; the
modules that call the participant (`Icoord`, `Send`, `GParti`, `H2/Base`, `H2c2/ExecOverwrite`,
and the handlers above them) take it as an instance argument, and `Replica2/Results.lean` closes it
with `H1/Parti.lean`'s proofs (`gryffPartiDeps_holds`, a local instance there). No `instance` of the
class exists.
-/
module

public import Dsverify.Proof.gryff.H1.Write2
public import Dsverify.Proof.gryff.H1.Read
public import Dsverify.Proof.gryff.H1.Write1
public import Dsverify.Proof.gryff.H1.Pure
public import Dsverify.GeneratedProof.gryff.examples.gryffnet
public import Dsverify.Proof.gryff.Lib.SortHyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB RecoveryInstance Proposal ReadOp WriteOp OngoingOp
  Msg Ev Ext Out Cmd Deps AMap StepRes)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF]
variable [sortA : SortSliceHyp GF]
variable [strconvA : strconv.Assumptions] -- N-5

/-- The triple of `H1/Parti.lean`'s `GryffParticipant.GetStoreMetadata.wp_proof`. -/
def GryffParticipant.GetStoreMetadata.spec : Prop :=
  ∀ (pa : Loc) (ip : GoInterface) (k : Fin 3) (tag : model.Tag) (ong : AMap 32 w32),
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗ partiOwn pa ip k tag ong }}
      (App (partiM pa go!"GetStoreMetadata") (Val #(W64 0)))
    {{ (md : Loc), RET #md; ∃ (tp : Loc) (gt : src.gryffproto.Tag), ⌜tagOf gt = tag⌝ ∗ tp ↦□ gt ∗
        md.[src.gryffcommon.StoreMetadata, go!"Tag"] ↦ tp ∗
        (md.[src.gryffcommon.StoreMetadata, go!"Tag"] ↦ tp -∗ partiOwn pa ip k tag ong) }}

/-- The triple of `H1/Parti.lean`'s `GryffParticipant.HandleOverwrite.wp_proof`. -/
def GryffParticipant.HandleOverwrite.spec : Prop :=
  ∀ (pa : Loc) (ip : GoInterface) (k : Fin 3) (V : w64 → IProp GF) (vt : model.ValTag)
     (ong : AMap 32 w32) (v : w64) (tp : Loc) (gt : src.gryffproto.Tag),
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗ partiOwn pa ip k vt.t ong ∗
        ipartiOk ip V ∗ V vt.v ∗ tp ↦□ gt }}
      (App (App (App (partiM pa go!"HandleOverwrite") (Val #(W64 0))) (Val #v)) (Val #tp))
    {{ RET #(); partiOwn pa ip k (ovw vt v (tagOf gt)).t ong ∗ V (ovw vt v (tagOf gt)).v }}

/-- The triple of `H1/Parti.lean`'s `GryffParticipant.HandleWrite2.wp_proof`. -/
def GryffParticipant.HandleWrite2.spec : Prop :=
  ∀ (pa : Loc) (ip : GoInterface) (k : Fin 3) (V : w64 → IProp GF) (s s' : RState) (o1 : Out)
     (m : model.Write2ProxiedM) (gv : src.gryffproto.ValTag) (hv : vtOf gv = m.vt)
     (hid : s.id = rid32 k) (hstep : model.stepWrite2 s m = .ok (s', [o1])),
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗
        partiOwn pa ip k s.tag s.ongoing ∗ ipartiOk ip V ∗ V s.val }}
      (App (App (App (App (partiM pa go!"HandleWrite2") (Val #m.k)) (Val #gv))
        (Val #m.requestId)) (Val #m.clientId))
    {{ (rp : Loc), RET #rp; partiOwn pa ip k s'.tag s'.ongoing ∗ V s'.val ∗
        ∃ g : src.gryffproto.Write2Reply, rp ↦ g ∗
          ⌜model.sendTo m.replicaId (.write2Reply (write2ReplyOf g)) = some o1⌝ }}

/-- The triple of `H1/Parti.lean`'s `GryffParticipant.HandleRead2.wp_proof`. -/
def GryffParticipant.HandleRead2.spec : Prop :=
  ∀ (pa : Loc) (ip : GoInterface) (k : Fin 3) (V : w64 → IProp GF) (s s' : RState) (o1 : Out)
     (m : model.Read2ProxiedM) (gv : src.gryffproto.ValTag) (uid : w64) (hv : vtOf gv = m.vt)
     (hstep : model.stepRead2 s m = .ok (s', [o1])),
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗
        partiOwn pa ip k s.tag s.ongoing ∗ ipartiOk ip V ∗ V s.val }}
      (App (App (App (App (App (partiM pa go!"HandleRead2") (Val #m.k)) (Val #gv))
        (Val #m.requestId)) (Val #m.clientId)) (Val #uid))
    {{ (rp : Loc), RET #rp; partiOwn pa ip k s'.tag s'.ongoing ∗ V s'.val ∗
        ∃ g : src.gryffproto.Read2Reply, rp ↦ g ∗
          ⌜model.sendTo m.replicaId (.read2Reply (read2ReplyOf g)) = some o1⌝ }}

/-- The triple of `H1/Parti.lean`'s `GryffParticipant.HandleRead1.wp_proof`. -/
def GryffParticipant.HandleRead1.spec : Prop :=
  ∀ (pa : Loc) (ip : GoInterface) (k : Fin 3) (V : w64 → IProp GF) (s s' : RState) (o1 : Out)
     (m : model.Read1ProxiedM) (dp vp : Loc) (gd : src.gryffproto.Dep)
     (gv : src.gryffproto.ValTag) (hd : depOf gd = m.d) (hv : vtOf gv = m.vt)
     (hid : s.id = rid32 k) (hstep : model.stepRead1 s m = .ok (s', [o1])),
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗
        partiOwn pa ip k s.tag s.ongoing ∗ ipartiOk ip V ∗ V s.val ∗ dp ↦□ gd ∗ vp ↦□ gv }}
      (App (App (App (App (App (App (App (partiM pa go!"HandleRead1") (Val #m.k)) (Val #dp))
        (Val #m.requestId)) (Val #m.clientId)) (Val #true)) (Val #vp)) (Val #m.replicaId))
    {{ (rp : Loc), RET #rp; partiOwn pa ip k s'.tag s'.ongoing ∗ V s'.val ∗
        ∃ g : src.gryffproto.Read1Reply, rp ↦ g ∗
          ⌜model.sendTo m.replicaId (.read1Reply (read1ReplyOf g)) = some o1⌝ }}

/-- The triple of `H1/Parti.lean`'s `GryffParticipant.HandleWrite1.wp_proof`. -/
def GryffParticipant.HandleWrite1.spec : Prop :=
  ∀ (pa : Loc) (ip : GoInterface) (k : Fin 3) (V : w64 → IProp GF) (s s' : RState)
     (outs : List Out) (m : model.Write1ProxiedM) (val : w64) (n : w32) (dp mp : Loc)
     (gd : src.gryffproto.Dep) (gmt : src.gryffproto.Tag) (hd : depOf gd = m.d)
     (hid : s.id = rid32 k) (hstep : model.stepWrite1 s m = .ok (s', outs)),
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryffcommon ∗
        partiOwn pa ip k s.tag s.ongoing ∗ ipartiOk ip V ∗ V s.val ∗ dp ↦□ gd ∗ mp ↦□ gmt }}
      (App (App (App (App (App (App (App (App (App (partiM pa go!"HandleWrite1") (Val #m.k))
        (Val #val)) (Val #n)) (Val #dp)) (Val #m.requestId)) (Val #m.clientId)) (Val #mp))
        (Val #m.forceWrite)) (Val #m.replicaId))
    {{ (rp : Loc), RET #rp; partiOwn pa ip k s'.tag s'.ongoing ∗ V s'.val ∗
        ((⌜rp = Loc.null ∧ outs = []⌝) ∨ ∃ (g : src.gryffproto.Write1Reply) (o1 : Out),
          rp ↦ g ∗ ⌜outs = [o1] ∧ model.sendTo m.replicaId (.write1Reply (write1ReplyOf g)) = some o1⌝) }}

/-- The participant's methods the coordinator and the handlers call (the file header). -/
class GryffPartiDeps : Prop where
  getStoreMetadata : GryffParticipant.GetStoreMetadata.spec (GF := GF) (hG := hG)
  handleOverwrite : GryffParticipant.HandleOverwrite.spec (GF := GF) (hG := hG)
  handleWrite2 : GryffParticipant.HandleWrite2.spec (GF := GF) (hG := hG)
  handleRead2 : GryffParticipant.HandleRead2.spec (GF := GF) (hG := hG)
  handleRead1 : GryffParticipant.HandleRead1.spec (GF := GF) (hG := hG)
  handleWrite1 : GryffParticipant.HandleWrite1.spec (GF := GF) (hG := hG)

end

end Perennial.gryff.replica2
