/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/Rcvr.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The replica's receiver meets `sp.replicaRpcSpec` through the kit's dispatch (`rpcCall`'s
`*swift.Replica` case: `BeTheLeader`, `Ping`), over `BeTheLeader`'s spec and the specs of the
kit's codec functions the dispatch calls (decoding `BeTheLeaderArgs`/`PingArgs`, encoding the
replies). The codec functions' specs are stated here as the master's are in
`Spec/swiftnet/CodecFns.lean` (owner: the codec group, which proves them; request in
notes/prove-swift.md), hypotheses, not unfolded.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.BeTheLeader
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.CodecFns
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Codec

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [examples.swiftnet.Assumptions]

/-- `rpcDecodeAs_defs_BeTheLeaderArgs(data)` on its encoding. -/
abbrev examples.swiftnet.rpcDecodeAs_defs_BeTheLeaderArgs.spec : Prop :=
  ∀ (data : GoSlice) (dq : DFrac),
  {{ (data ↦*{dq} sp.KitVal.beTheLeaderArgs.encode : IProp netDistGF) }}
    (App (Val (@! examples.swiftnet.rpcDecodeAs_defs_BeTheLeaderArgs)) (Val #data))
  {{ RET (PairV #(replica.defs.BeTheLeaderArgs.mk) #(interface.nil : GoInterface));
      data ↦*{dq} sp.KitVal.beTheLeaderArgs.encode }}

/-- `rpcDecodeAs_defs_PingArgs(data)` on a `PingArgs`' encoding. -/
abbrev examples.swiftnet.rpcDecodeAs_defs_PingArgs.spec : Prop :=
  ∀ (data : GoSlice) (dq : DFrac) (a : w8),
  {{ (data ↦*{dq} (sp.KitVal.pingArgs a).encode : IProp netDistGF) }}
    (App (Val (@! examples.swiftnet.rpcDecodeAs_defs_PingArgs)) (Val #data))
  {{ RET (PairV #(replica.defs.PingArgs.mk a) #(interface.nil : GoInterface));
      data ↦*{dq} (sp.KitVal.pingArgs a).encode }}

/-- `rpcEnc_defs_BeTheLeaderReply(b, v)`: appends `v`'s encoding. -/
abbrev examples.swiftnet.rpcEnc_defs_BeTheLeaderReply.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (v : replica.defs.BeTheLeaderReply),
  {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp netDistGF) }}
    (App (App (Val (@! examples.swiftnet.rpcEnc_defs_BeTheLeaderReply)) (Val #b)) (Val #v))
  {{ (b' : GoSlice), RET #b'; b' ↦* (bs ++ (sp.cI32 v.Leader' ++ sp.cI32 v.NextLeader')) ∗
      ownSliceCap w8 b' (DFrac.own 1) }}

/-- `rpcEnc_defs_PingReply(b, v)`: appends nothing. -/
abbrev examples.swiftnet.rpcEnc_defs_PingReply.spec : Prop :=
  ∀ (b : GoSlice) (bs : List w8) (v : replica.defs.PingReply),
  {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp netDistGF) }}
    (App (App (Val (@! examples.swiftnet.rpcEnc_defs_PingReply)) (Val #b)) (Val #v))
  {{ (b' : GoSlice), RET #b'; b' ↦* bs ∗ ownSliceCap w8 b' (DFrac.own 1) }}

end spec

section spec2
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [examples.swiftnet.Assumptions]

/-- The replica's receiver (persistent): from `rcvrRes`, it meets the replicas' service. -/
abbrev swift.rcvr.spec : Prop :=
  ∀ (r : Loc) (γc γm : GName),
  isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
    swift.rcvrRes r γc γm ⊢
    net.rpc.rcvrOk (interface.mkOk (go.GoType.PointerType swift.Replica.ty) #r)
      (sp.replicaRpcSpec γc γm)

end spec2

theorem swift.enc_beTheLeaderReply (l n : w32) :
    (sp.KitVal.beTheLeaderReply l n).encode = sp.cU64 (W64 10) ++ (sp.cI32 l ++ sp.cI32 n) := rfl

theorem swift.enc_pingReply : sp.KitVal.pingReply.encode = sp.cU64 (W64 8) ++ [] := rfl

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions] [replica.Assumptions] [github_com.orcaman.concurrent_map.Assumptions]
  [sync.Assumptions] [examples.swiftnet.Assumptions]

set_option maxHeartbeats 4000000 in
theorem swift.rcvr.wp_proof
    (wp_BTL : swift.Replica.BeTheLeader.spec)
    (wp_decB : examples.swiftnet.rpcDecodeAs_defs_BeTheLeaderArgs.spec)
    (wp_decP : examples.swiftnet.rpcDecodeAs_defs_PingArgs.spec)
    (wp_put : examples.swiftnet.rpcPutU64.specNil)
    (wp_encB : examples.swiftnet.rpcEnc_defs_BeTheLeaderReply.spec)
    (wp_encP : examples.swiftnet.rpcEnc_defs_PingReply.spec) :
    swift.rcvr.spec := by
  intro r γc γm
  iintro ⟨#Hpkg, #Hres⟩
  unfold net.rpc.rcvrOk
  imodintro
  iintro %meth %args %Φ HS
  unfold net.rpc.RpcCodec.call kitCodec
  simp only
  iintro %s %dq Hs
  have hfn : net.rpc.kitFn go!"rpcCall" = functions examples.swiftnet.rpcCall [] := rfl
  rw [hfn]
  wp_func_call
  wp_call
  wp_auto
  wp_if_destruct
  · -- BeTheLeader
    ihave HS := (sp.replicaRpcSpec_beTheLeader (γc := γc) (γm := γm) args Φ).1 $$ HS
    icases HS with ⟨%Hargs, HΦ⟩
    subst Hargs
    wp_func_call
    wp_call
    wp_auto
    wp_apply wp_decB $$ [$Hs] as Hs
    wp_apply wp_BTL $$ [$Hres $«$r0»] as ⟨%ld, %nl, Hrep, Hok⟩
    wp_apply wp_put as %b ⟨Hb, Hcb⟩
    wp_apply wp_encB $$ [$Hb $Hcb] as %b' ⟨Hb', Hcb'⟩
    simp only [← swift.enc_beTheLeaderReply]
    iexists b', _, [], true
    isplitr
    · ipureintro; rfl
    isplitl [Hb']
    · iexact Hb'
    isplitr
    · ipureintro; rfl
    iapply HΦ $$ Hok
  wp_if_destruct
  · -- Ping
    ihave HS := (sp.replicaRpcSpec_ping (γc := γc) (γm := γm) args Φ).1 $$ HS
    icases HS with ⟨%a, %Hargs, HΦ⟩
    subst Hargs
    wp_func_call
    wp_call
    wp_auto
    wp_apply wp_decP $$ [$Hs] as Hs
    iunfold swift.rcvrRes at Hres
    icases Hres with ⟨%rr, %N, %fr, %l, %me, %dm, %qs, %rc, %γrc, %γdl, #Hrr, -⟩
    wp_method_call
    wp_call
    wp_auto
    wp_method_call
    wp_call
    wp_auto
    wp_apply wp_put as %b ⟨Hb, Hcb⟩
    wp_apply wp_encP $$ [$Hb $Hcb] as %b' ⟨Hb', Hcb'⟩
    rw [show sp.cU64 (W64 8) = sp.KitVal.pingReply.encode from rfl]
    iexists b', _, [], true
    isplitr
    · ipureintro; rfl
    isplitl [Hb']
    · iexact Hb'
    isplitr
    · ipureintro; rfl
    iexact HΦ
  -- another method: excluded by the spec
  iexfalso
  iapply sp.replicaRpcSpec_other (γc := γc) (γm := γm) meth args Φ ⟨by assumption,
    by assumption⟩ $$ HS

end proof

end Perennial.github_com.imdea_software.swiftpaxos
