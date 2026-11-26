/-
The kit's generated codec (`examples/craqnet/rpc_gen.go`, by `models/net/rpc/rpcgen.py`) as the
specs see it.

**The `CodecSpec`** (`craqCodec`): each predicate transformer is the weakest precondition of the
generated function it describes (`rpcEncode`, `rpcDecode`, `rpcReceiver`), so the codec meets it by definition
(`craqCodec_encOk`, `craqCodec_decOk`, `craqCodec_rcvOk`), and `rpcReady` (net/rpc initialized, the codec registered)
is what the clients need. The facts a proof needs are the codec lemmas below (the lab's): per wire
type, what encoding a Go value gives (`Wire.lean`'s, rpcgen's bytes), and that decoding a reply
into a fresh zero value is safe and, on success, gives back the value of an encoding.

**H5** (notes/dsv-craq.md): the codec lemmas `enc_*`, `dec_*` are stated here and proved in
`CodecProof.lean` (`craqCodecLaws`); the decoding lemmas assume the reply's type tag is the
target's (`tagOk`), see "Decoding the replies".
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.Iface
public import Dsverify.Proof.github_com.despreston.go_craq.examples.craqnet.Base
public import Net.Proof.net.rpc.Codec

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.despreston.go_craq

/-- A pointer to a struct as an interface value. -/
abbrev ptrIface [GooseExts] [GoGlobalContext] (t : go.GoType) (p : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType t) #p

section codec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [π : NetProtoGS]
variable [store.Assumptions] [transport.Assumptions] [transport.netrpc.Assumptions]
variable [examples.craqnet.Assumptions]


attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The codec's predicate transformers: the generated functions' weakest preconditions. -/
def craqCodec : net.rpc.CodecSpec GF where
  enc v Ψ := iprop(∀ Φ : val → IProp GF,
    ▷ (∀ (sl : GoSlice) (bs : List w8), sl ↦* bs -∗ ownSliceCap w8 sl (DFrac.own 1) -∗ Ψ bs -∗
        Φ #sl) -∗
    WP (App (Val #(functions examples.craqnet.rpcEncode [])) (Val #v)) {{ Φ }})
  dec bs ptr Ψ := iprop(∀ (data : GoSlice) (dq : DFrac) (Φ : val → IProp GF),
    data ↦*{dq} bs -∗
    ▷ (∀ (err : GoInterface) (ok : Bool), data ↦*{dq} bs -∗ ⌜err = interface.nil ↔ ok = true⌝ -∗
        Ψ ok -∗ (if ok then iprop(True) else net.rpc.decErr err) -∗ Φ #err) -∗
    WP (App (App (Val #(functions examples.craqnet.rpcDecode [])) (Val #data)) (Val #ptr)) {{ Φ }})
  rcv rcvr Ψ := iprop(∀ Φ : val → IProp GF, ▷ (∀ rp : Loc, Ψ rp -∗ Φ #rp) -∗
    WP (App (Val #(functions examples.craqnet.rpcReceiver [])) (Val #rcvr)) {{ Φ }})

theorem craqCodec_encOk : ⊢ net.rpc.encOk (hG := hG) craqCodec (functions examples.craqnet.rpcEncode []) := by
  unfold net.rpc.encOk
  iintro !> %v %Ψ %Φ Henc HΦ
  unfold craqCodec
  iapply Henc
  iexact HΦ

theorem craqCodec_rcvOk : ⊢ net.rpc.rcvOk (hG := hG) craqCodec (functions examples.craqnet.rpcReceiver []) := by
  unfold net.rpc.rcvOk
  iintro !> %rcvr %Ψ %Φ Hr HΦ
  unfold craqCodec
  iapply Hr
  iexact HΦ

theorem craqCodec_decOk : ⊢ net.rpc.decOk (hG := hG) craqCodec (functions examples.craqnet.rpcDecode []) := by
  unfold net.rpc.decOk
  iintro !> %data %dq %bs %ptr %Ψ %Φ Hd Hdec HΦ
  unfold craqCodec
  iapply Hdec $$ Hd
  iexact HΦ

/-- A machine's net/rpc and net/http environment (persistent): what Net's `rpc.DialHTTP.spec`
asks besides the address (`receiptBound ≤ 2 ^ 64`, net/rpc's `cliEnv`, here inside its server's
`srvEnv`, net/http's `httpEnv`, net/rpc's `connected`), the net/rpc server's `srvEnv` and the
`connected` its `ServeHTTP` writes. net/rpc and net/http are names-only packages (their facts are
`True`), so a machine's boot supplies the package variables (`rpcBootRes`); the bound is the
deployment's. -/
def rpcEnv : IProp GF :=
  iprop(⌜receiptBound GF ≤ 2 ^ 64⌝ ∗ net.rpc.srvEnv ∗ net.http.httpEnv ∗
    globalAddr net.rpc.connected ↦□ net.rpc.connectedStatus)

instance rpcEnv_persistent : Persistent (rpcEnv (hG := hG)) := by
  unfold rpcEnv; infer_instance

/-- net/rpc is initialized, the kit's codec registered, and the machine's environment (persistent). -/
def rpcReady : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ net.rpc.codecSet craqCodec ∗ rpcEnv)

instance rpcReady_persistent : Persistent (rpcReady (hG := hG)) := by
  unfold rpcReady; infer_instance

/-! ## Encoding the arguments -/

abbrev enc_string.spec : Prop :=
  ∀ (s : GoString) (Ψ : List w8 → IProp GF),
    Ψ (encString s) ⊢ craqCodec.enc (interface.mkOk go.string #s) Ψ

abbrev enc_EmptyArgs.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (Ψ : List w8 → IProp GF),
    p ↦{dq} transport.netrpc.EmptyArgs.mk ∗
      (p ↦{dq} transport.netrpc.EmptyArgs.mk -∗ Ψ encEmptyArgs) ⊢
    craqCodec.enc (ptrIface transport.netrpc.EmptyArgs.ty p) Ψ

abbrev enc_NodeMeta.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (m : MetaV) (Ψ : List w8 → IProp GF),
    metaPtr p dq m ∗ (metaPtr p dq m -∗ Ψ (encMeta m)) ⊢
    craqCodec.enc (ptrIface transport.NodeMeta.ty p) Ψ

abbrev enc_CommitArgs.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (k : GoString) (v : w64) (Ψ : List w8 → IProp GF),
    p ↦{dq} transport.netrpc.CommitArgs.mk k v ∗
      (p ↦{dq} transport.netrpc.CommitArgs.mk k v -∗ Ψ (encCommitArgs k v)) ⊢
    craqCodec.enc (ptrIface transport.netrpc.CommitArgs.ty p) Ψ

abbrev enc_WriteArgs.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (k : GoString) (sl : GoSlice) (dqs : DFrac)
    (x : GoString) (v : w64) (Ψ : List w8 → IProp GF),
    p ↦{dq} transport.netrpc.WriteArgs.mk k sl v ∗ sl ↦*{dqs} x ∗
      (p ↦{dq} transport.netrpc.WriteArgs.mk k sl v -∗ sl ↦*{dqs} x -∗
        Ψ (encWriteArgs k x v)) ⊢
    craqCodec.enc (ptrIface transport.netrpc.WriteArgs.ty p) Ψ

abbrev enc_ClientWriteArgs.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (k : GoString) (sl : GoSlice) (dqs : DFrac)
    (x : GoString) (Ψ : List w8 → IProp GF),
    p ↦{dq} transport.netrpc.ClientWriteArgs.mk k sl ∗ sl ↦*{dqs} x ∗
      (p ↦{dq} transport.netrpc.ClientWriteArgs.mk k sl -∗ sl ↦*{dqs} x -∗
        Ψ (encClientWriteArgs k x)) ⊢
    craqCodec.enc (ptrIface transport.netrpc.ClientWriteArgs.ty p) Ψ

abbrev enc_PropagateRequest.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (req : GMap GoString w64)
    (Ψ : List w8 → IProp GF),
    reqPtr p dq req ∗ (reqPtr p dq req -∗ ∀ bs, ⌜encPropReq req bs⌝ -∗ Ψ bs) ⊢
    craqCodec.enc (ptrIface transport.PropagateRequest.ty p) Ψ

/-! ## Decoding the replies

`rpcDecode(data, ptr)` reads `data`'s type tag and **panics** (`rpcNotModelled`) when the tag parses
but names another type than `ptr`'s: so each decoding lemma assumes `tagOk t rep` (the tag, if it
parses, is the target's). Net's `Client.Call.spec` asks for decoding only of the method's answers
(`Φ rep []` in hand); the clients derive `tagOk` from the method's answer (`Netrpc/Defs.lean`'s
`wp_Call_tag`). A failed decoding leaves the fields decoded before the
failure written: the failure branches give some field values. -/

/-- The pure `rpcGetU64`. -/
def getU64 (bs : List w8) : Option (w64 × List w8) :=
  if 8 ≤ bs.length then some (leToU64 (bs.take 8), bs.drop 8) else none

/-- The pure `rpcGetTag` (and `rpcDec_t5`): a length, then that many bytes. -/
def getTag (bs : List w8) : Option (GoString × List w8) :=
  match getU64 bs with
  | some (n, r) => if uint.nat n ≤ r.length then some (r.take (uint.nat n), r.drop (uint.nat n)) else none
  | none => none

/-- `rep`'s type tag, if it parses, is `t`. -/
def tagOk (t : GoString) (rep : List w8) : Prop :=
  ∀ t' rest, getTag rep = some (t', rest) → t' = t

theorem getU64_enc (x : w64) (rest : List w8) : getU64 (u64Le x ++ rest) = some (x, rest) := by
  unfold getU64
  rw [ite_eq_left (by simp [u64Le_length])]
  have h8 := u64Le_length x
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append,
    u64Le_to_word]

theorem getTag_encStr (s : GoString) (rest : List w8) (hs : s.length < 2 ^ 64) :
    getTag (encStr s ++ rest) = some (s, rest) := by
  unfold getTag encStr
  rw [List.append_assoc, getU64_enc]
  have hn : uint.nat (W64 s.length) = s.length := by
    show (BitVec.ofNat 64 s.length).toNat = s.length
    simp only [BitVec.toNat_ofNat]; omega
  simp only [hn, List.length_append, Nat.le_add_right, ite_true, List.take_left', List.drop_left']

theorem tagOk_tagged (t : GoString) (body : List w8) (ht : t.length < 2 ^ 64) :
    tagOk t (tagged t body) := by
  intro t' rest h
  unfold tagged at h
  rw [getTag_encStr t body ht] at h
  cases h; rfl

abbrev dec_EmptyReply.spec : Prop :=
  ∀ (p : Loc) (rep : List w8) (Ψ : Bool → IProp GF),
    ⌜tagOk go!"github.com/despreston/go-craq/transport/netrpc.EmptyReply" rep⌝ ∗
    p ↦ transport.netrpc.EmptyReply.mk ∗ (∀ ok, p ↦ transport.netrpc.EmptyReply.mk -∗ Ψ ok) ⊢
    craqCodec.dec rep (ptrIface transport.netrpc.EmptyReply.ty p) Ψ

abbrev dec_VersionResponse.spec : Prop :=
  ∀ (p : Loc) (rep : List w8) (Ψ : Bool → IProp GF),
    ⌜tagOk go!"github.com/despreston/go-craq/transport/netrpc.VersionResponse" rep⌝ ∗
    p ↦ transport.netrpc.VersionResponse.mk go!"" (W64 0) ∗
      (∀ ok, (if ok then ∃ (k : GoString) (v : w64), p ↦ transport.netrpc.VersionResponse.mk k v ∗
          ⌜∀ k' v', rep = encVersionResp k' v' → k = k' ∧ v = v'⌝
        else ∃ (k : GoString) (v : w64), p ↦ transport.netrpc.VersionResponse.mk k v) -∗ Ψ ok) ⊢
    craqCodec.dec rep (ptrIface transport.netrpc.VersionResponse.ty p) Ψ

abbrev dec_Item.spec : Prop :=
  ∀ (p : Loc) (rep : List w8) (Ψ : Bool → IProp GF),
    ⌜tagOk go!"github.com/despreston/go-craq/transport.Item" rep⌝ ∗
    p ↦ transport.Item.mk go!"" slice.nil ∗
      (∀ ok, (if ok then ∃ (k : GoString) (sl : GoSlice) (x : GoString),
          p ↦ transport.Item.mk k sl ∗ sl ↦* x ∗ ⌜∀ k' x', rep = encItem k' x' → k = k' ∧ x = x'⌝
        else ∃ (k : GoString) (sl : GoSlice), p ↦ transport.Item.mk k sl) -∗ Ψ ok) ⊢
    craqCodec.dec rep (ptrIface transport.Item.ty p) Ψ

abbrev dec_NodeMeta.spec : Prop :=
  ∀ (p : Loc) (rep : List w8) (Ψ : Bool → IProp GF),
    ⌜tagOk go!"github.com/despreston/go-craq/transport.NodeMeta" rep⌝ ∗
    metaPtr p (DFrac.own 1) ⟨false, false, go!"", go!"", go!""⟩ ∗
      (∀ ok, (∃ m : MetaV, metaPtr p (DFrac.own 1) m) -∗ Ψ ok) ⊢
    craqCodec.dec rep (ptrIface transport.NodeMeta.ty p) Ψ

abbrev dec_PropagateResponse.spec : Prop :=
  ∀ (p mp : Loc) (rep : List w8) (Ψ : Bool → IProp GF),
    ⌜tagOk go!"github.com/despreston/go-craq/transport.PropagateResponse" rep⌝ ∗
    p ↦ mp ∗ ownMap mp (DFrac.own 1) (∅ : GMap GoString GoSlice) ∗
      (∀ ok, (if ok then ∃ resp, respPtr p resp ∗ ⌜∀ r, encPropResp r rep → resp = r⌝
        else ∃ mp' : Loc, p ↦ mp') -∗ Ψ ok) ⊢
    craqCodec.dec rep (ptrIface transport.PropagateResponse.ty p) Ψ

/-- The codec lemmas (hypothesis H5). -/
structure CodecLaws : Prop where
  enc_string : enc_string.spec (GF := GF)
  enc_EmptyArgs : enc_EmptyArgs.spec (GF := GF)
  enc_NodeMeta : enc_NodeMeta.spec (GF := GF)
  enc_CommitArgs : enc_CommitArgs.spec (GF := GF)
  enc_WriteArgs : enc_WriteArgs.spec (GF := GF)
  enc_ClientWriteArgs : enc_ClientWriteArgs.spec (GF := GF)
  enc_PropagateRequest : enc_PropagateRequest.spec (GF := GF)
  dec_EmptyReply : dec_EmptyReply.spec (GF := GF)
  dec_VersionResponse : dec_VersionResponse.spec (GF := GF)
  dec_Item : dec_Item.spec (GF := GF)
  dec_NodeMeta : dec_NodeMeta.spec (GF := GF)
  dec_PropagateResponse : dec_PropagateResponse.spec (GF := GF)

end codec

end github_com.despreston.go_craq

end Perennial
