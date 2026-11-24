/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/ConnectSpecs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`Connect`'s internal specs (the client package's unexported helpers) and the pure facts its
proof uses.

* `dialMaster.specI`: `fmt.Sprintf("%s:%d", ...)` is the master's address; up to three
  `rpc.DialHTTP`s: an rpc client of the master stored in `c.master`, or an error (nothing stored);
* `call.specI`: `r.Call` in a goroutine, its result sent on a buffered channel (a bag carrying
  the call's postcondition), and a `select` with `time.After`: the call's result, or an error
  (a timeout: the goroutine keeps the arguments and the reply);
* `callMasterRL.specI` / `callMasterL.specI`: up to 100 calls of the master's `GetReplicaList` /
  `GetLeader` (the frozen `masterSpec`'s laws; the kit codec's decoding into a fresh reply):
  the decoded reply (for `GetReplicaList`: the membership `nodes` with `cfg`, `Ready` set), or an
  error;
* `findClosest.specI`: no error; only `Ping` and `ClosestId` change;
* `dial.specI`: up to three `net.DialTimeout`s: a connection with its end's tokens and fresh
  token, or an error.

Pure: `masterAddr_port` (the master's address determines its port), `grl_inj` (the codec's
encoding of a `GetReplicaListReply` is injective, from the codec group's round trip),
`nodes_body_bound`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.PkgFacts
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.RpcHttpHyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.master.Addr
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.KitLike

-- PORT: lab imports dropped: Harness.Proof.net.rpc.Results, Harness.Proof.net.DialTimeout

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace client.cn

/-! ## Pure facts -/

/-- The master's address names port 7001. -/
theorem masterAddr_port {ip : GoString} {port : w64} (h : sp.addrPort ip port = masterAddr) :
    port = W64 7001 := by
  have hm : masterAddr = go!"127.0.0.1" ++ W8 58 :: Perennial.fmt.decimalNat 7001 := by
    simp [Perennial.fmt.decimalNat_eq, Perennial.fmt.digitByte, masterAddr]
  rw [hm] at h
  unfold sp.addrPort at h
  have hd : (Nat.toDigits 10 port.toNat).map (fun ch => W8 ch.toNat) =
      (Nat.toDigits 10 port.toNat).map master.digitW8 := rfl
  rw [hd, List.append_assoc, List.singleton_append, master.decimalNat_toDigits] at h
  obtain ⟨-, h2⟩ := master.split_last (master.colon_not_mem_digits _)
    (master.colon_not_mem_digits _) h
  have := master.toDigits_inj h2
  apply BitVec.eq_of_toNat_eq
  rw [this]
  simp only [W64, BitVec.toNat_ofInt]
  omega

-- (The lab codec's injectivity facts `grl_inj`, `nodes_body_bound`, `merge_grl` are gone with
-- the codec switch: `dec_GetReplicaListReply` gives the fields of a decoded encoding.)

end client.cn

/-! ## The internal specs -/

/-- (An unfold of the harness's `net.rpc.rpcAddr`: a missing persistence instance.) -/
instance client.cn.rpcAddr_persistent [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
    [GoGlobalContext] [hG : HeapGS HasLC.hasLC netDistGF] [NetProtoGS]
    (W : net.rpc.RpcWorld netDistGF) (a : GoString) :
    Persistent (net.rpc.rpcAddr (GF := netDistGF) W a) := by
  unfold net.rpc.rpcAddr; infer_instance

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [client.Assumptions] [net.Assumptions] [net.FieldAssumptions] [net.rpc.Assumptions]
variable [examples.swiftnet.Assumptions]
-- the codec (decision D6, Proof/swiftnet/KitLike.lean): `kitCodec` for the frozen statements,
-- `kitCodecC` in the link
variable [C : net.rpc.RpcCodec netDistGF]

variable [log.Assumptions] [net.http.Assumptions] [RpcHttpAddr netDistGF] [RpcHttpHyp netDistGF] in
/-- `c.dialMaster()` from no master client, at the master's address. -/
abbrev client.Client.dialMaster.specI : Prop :=
  ∀ (cl : Loc) (v : client.Client) (W : net.rpc.RpcWorld netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      cl ↦ v ∗ dlog.quiet v.Logger' ∗
      ⌜v.master' = null ∧ sp.addrPort v.masterAddr' v.masterPort' = masterAddr⌝ ∗
      rpcHttp W masterAddr }}
    (App (Val (cl @!! go.GoType.PointerType client.Client.ty @!! go!"dialMaster")) (Val #()))
  {{ (m : Loc) (err : GoInterface), RET (PairV #m #err);
      (⌜err = interface.nil⌝ ∗ cl ↦ { v with master' := m } ∗ net.rpc.isClient m W masterAddr) ∨
      (⌜err ≠ interface.nil⌝ ∗ cl ↦ v) }}

/-- `c.call(r, sm, args, reply)`: `Call`'s precondition (with the request's bound: it fits the
frames the net/rpc model's server reads, `maxFrameN`); its result, or an error (then the
goroutine keeps what it was given). -/
abbrev client.Client.call.specI : Prop :=
  ∀ (cl : Loc) (v : client.Client) (r : Loc) (W : net.rpc.RpcWorld netDistGF)
    (a sm svc M : GoString) (S : net.rpc.MethodSpec netDistGF) (args reply : GoInterface)
    (Φ : List w8 → GoString → IProp netDistGF) (Rargs D : IProp netDistGF)
    (Θ : List w8 → Bool → IProp netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      cl ↦ v ∗ dlog.quiet v.Logger' ∗
      net.rpc.codecSet (GF := netDistGF) net.rpc.RpcCodec.spec ∗ net.rpc.kitCodecOk ∗
      net.rpc.isClient r W a ∗
      ⌜net.rpc.splitSM sm = some (svc, M) ∧ W.SS a svc = some S ∧ reply ≠ interface.nil⌝ ∗
      ⌜sm.length + 16 ≤ net.rpc.maxFrameN⌝ ∗
      net.rpc.RpcCodec.enc args (fun bs => iprop(⌜bs.length ≤ net.rpc.maxFrameN⌝ ∗ S M bs Φ ∗ Rargs)) ∗ D ∗
      □ (D -∗ ∀ rep, Φ rep [] -∗ net.rpc.RpcCodec.dec rep reply (Θ rep)) }}
    (App (App (App (App (Val (cl @!! go.GoType.PointerType client.Client.ty @!! go!"call"))
      (Val #r)) (Val #sm)) (Val #args)) (Val #reply))
  {{ (err : GoInterface), RET #err; cl ↦ v ∗
      ((⌜err = interface.nil⌝ ∗ Rargs ∗ ∃ rep, Θ rep true) ∨
        ⌜err ≠ interface.nil⌝) }}

/-- `c.callMaster("GetReplicaList")`: the membership, `Ready`, or an error. -/
abbrev client.Client.callMasterRL.specI : Prop :=
  ∀ (cl : Loc) (v : client.Client) (W : net.rpc.RpcWorld netDistGF) (γc γm : GName),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      cl ↦ v ∗ dlog.quiet v.Logger' ∗
      net.rpc.codecSet (GF := netDistGF) net.rpc.RpcCodec.spec ∗ net.rpc.kitCodecOk ∗
      net.rpc.isClient v.master' W masterAddr ∗
      ⌜W.SS masterAddr go!"Master" = some (withErr (sp.masterSpec γc γm))⌝ }}
    (App (Val (cl @!! go.GoType.PointerType client.Client.ty @!! go!"callMaster"))
      (Val #(go!"GetReplicaList")))
  {{ (res err : GoInterface), RET (PairV #res #err); cl ↦ v ∗
      ((⌜err = interface.nil⌝ ∗ ∃ (p : Loc) (s1 s2 : GoSlice) (nodes : List GoString)
          (alive : List Bool) (fr : Bool),
        ⌜res = interface.mkOk (go.GoType.PointerType replica.defs.GetReplicaListReply.ty) #p⌝ ∗
        p ↦ (⟨s1, s2, true⟩ : replica.defs.GetReplicaListReply) ∗ s1 ↦* nodes ∗ s2 ↦* alive ∗
        sp.cfg γc γm nodes.length fr nodes ∗ ⌜alive.length = nodes.length⌝) ∨
       ⌜err ≠ interface.nil⌝) }}

/-- `c.callMaster("GetLeader")`: some leader id, or an error. -/
abbrev client.Client.callMasterL.specI : Prop :=
  ∀ (cl : Loc) (v : client.Client) (W : net.rpc.RpcWorld netDistGF) (γc γm : GName),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      cl ↦ v ∗ dlog.quiet v.Logger' ∗
      net.rpc.codecSet (GF := netDistGF) net.rpc.RpcCodec.spec ∗ net.rpc.kitCodecOk ∗
      net.rpc.isClient v.master' W masterAddr ∗
      ⌜W.SS masterAddr go!"Master" = some (withErr (sp.masterSpec γc γm))⌝ }}
    (App (Val (cl @!! go.GoType.PointerType client.Client.ty @!! go!"callMaster"))
      (Val #(go!"GetLeader")))
  {{ (res err : GoInterface), RET (PairV #res #err); cl ↦ v ∗
      ((⌜err = interface.nil⌝ ∗ ∃ (p : Loc) (id : w64),
        ⌜res = interface.mkOk (go.GoType.PointerType replica.defs.GetLeaderReply.ty) #p⌝ ∗
        p ↦ (⟨id⟩ : replica.defs.GetLeaderReply)) ∨
       ⌜err ≠ interface.nil⌝) }}

/-- `c.findClosest(alive)`: no error; only `Ping` and `ClosestId` change. -/
abbrev client.Client.findClosest.specI : Prop :=
  ∀ (cl : Loc) (v : client.Client) (asl : GoSlice) (alive : List Bool) (l : List GoString)
    (dq dq' : DFrac),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      cl ↦ v ∗ dlog.quiet v.Logger' ∗ ⌜v.Ping' = slice.nil ∧ alive.length = l.length⌝ ∗
      v.replicas' ↦*{dq} l ∗ asl ↦*{dq'} alive }}
    (App (Val (cl @!! go.GoType.PointerType client.Client.ty @!! go!"findClosest")) (Val #asl))
  {{ (err : GoInterface), RET #err; ⌜err = interface.nil⌝ ∗
      (∃ (p : GoSlice) (ci : w64), cl ↦ { v with Ping' := p, ClosestId' := ci }) ∗
      v.replicas' ↦*{dq} l ∗ asl ↦*{dq'} alive }}

/-- `c.dial(a)` of an address with its protocols: a fresh connection's end, or an error. -/
abbrev client.Client.dial.specI : Prop :=
  ∀ (cl : Loc) (v : client.Client) (a : GoString) (P Q : Proto netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      cl ↦ v ∗ dlog.quiet v.Logger' ∗ addrProto a P Q }}
    (App (Val (cl @!! go.GoType.PointerType client.Client.ty @!! go!"dial")) (Val #a))
  {{ (cv err : GoInterface), RET (PairV #cv #err); cl ↦ v ∗
      ((∃ (c : Loc) (cid : Nat),
        ⌜cv = interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c ∧ err = interface.nil⌝ ∗
        net.ownTCPConn c cid false ∗ connEnd cid false P Q [] [] ∗ connFresh cid false) ∨
       ⌜cv = interface.nil ∧ err ≠ interface.nil⌝) }}

end spec

end Perennial.github_com.imdea_software.swiftpaxos
