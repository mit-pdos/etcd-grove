/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/Rabia/Model.lean`, run `rabia-r1wake-1`;
`cmdInput`, the lab's map to its harness's key-value inputs, dropped: the kit's porcupine model is
`kit.go`'s, notes/dsv-rabia.md.)

The pure model of Rabia's data (interface, stage 1): the values of the messages Rabia sends
(`ObjV`, `MsgV`, `CmdV`, the records of `message.ConsensusObj`, `message.Msg`,
`message.Command`), their wire format (gogo-protobuf's proto3 encoding, as `message.pb.go`'s
generated `MarshalToSizedBuffer` writes it: fields in increasing number, a zero scalar omitted,
repeated `uint32`s packed), the framing of `message.BufWrite` (a 4-byte little-endian length,
then the bytes), and the key-value semantics of a client command (`proxy.naiveExecuteCmd`).
-/
module

public import Perennial.Proof.ProofPrelude

@[expose] public section

namespace Perennial.rabia.model

/-! ## Values -/

/-- A `message.ConsensusObj`: a proxy's batch of client requests (a proposal or a decision). -/
structure ObjV where
  proId : w32
  proSeq : w32
  svrSeq : w32
  isNull : Bool
  cliIds : List w32
  cliSeqs : List w32
  commands : List GoString
deriving DecidableEq, Inhabited

/-- A `message.Msg`: `ty` is the `MsgType` (an `int32`; Rabia's are 0..6). -/
structure MsgV where
  ty : w32
  phase : w32
  value : w32
  obj : Option ObjV
deriving DecidableEq, Inhabited

/-- A `message.Command`: a client's request or a proxy's reply. -/
structure CmdV where
  cliId : w32
  cliSeq : w32
  svrSeq : w32
  commands : List GoString
deriving DecidableEq, Inhabited

/-- The message types (`message.MsgType`). -/
def tyClientRequest : w32 := 0
def tyProposal : w32 := 1
def tyState : w32 := 2
def tyVote : w32 := 3
def tyProposalRequest : w32 := 4
def tyProposalReply : w32 := 5
def tyDecision : w32 := 6

/-- Two objects are the same consensus object (`message.ProxySeqIdEqual`). -/
def ObjV.sameId (a b : ObjV) : Bool := a.proSeq == b.proSeq && a.proId == b.proId

/-! ## The wire format -/

/-- A protobuf varint (base-128, least significant group first). -/
def varint (n : Nat) : List w8 :=
  if h : n < 128 then [BitVec.ofNat 8 n]
  else BitVec.ofNat 8 (n % 128 + 128) :: varint (n / 128)
termination_by n
decreasing_by omega

/-- A scalar field with tag byte `tag` (omitted when zero). -/
def encScalar (tag : w8) (n : Nat) : List w8 := if n = 0 then [] else tag :: varint n

/-- A length-delimited field. -/
def encBytes (tag : w8) (bs : List w8) : List w8 := tag :: varint bs.length ++ bs

/-- A repeated `uint32` field, packed (omitted when empty). -/
def encPacked (tag : w8) (ns : List w32) : List w8 :=
  if ns = [] then [] else encBytes tag (ns.flatMap fun n => varint n.toNat)

/-- `message.ConsensusObj`'s encoding (fields 1..7). -/
def encObj (o : ObjV) : List w8 :=
  encScalar 0x08 o.proId.toNat ++ encScalar 0x10 o.proSeq.toNat ++
  encScalar 0x18 o.svrSeq.toNat ++ (if o.isNull then [0x20, 1] else []) ++
  encPacked 0x2a o.cliIds ++ encPacked 0x32 o.cliSeqs ++
  o.commands.flatMap (encBytes 0x3a)

/-- An `int32` enum value as protobuf encodes it (sign-extended to 64 bits). -/
def enumNat (t : w32) : Nat := (BitVec.signExtend 64 t).toNat

/-- `message.Msg`'s encoding (fields 1..4). -/
def encMsg (m : MsgV) : List w8 :=
  encScalar 0x08 (enumNat m.ty) ++ encScalar 0x10 m.phase.toNat ++
  encScalar 0x18 m.value.toNat ++
  (match m.obj with | none => [] | some o => encBytes 0x22 (encObj o))

/-- `message.Command`'s encoding (fields 1..4). -/
def encCmd (c : CmdV) : List w8 :=
  encScalar 0x08 c.cliId.toNat ++ encScalar 0x10 c.cliSeq.toNat ++
  encScalar 0x18 c.svrSeq.toNat ++ c.commands.flatMap (encBytes 0x22)

/-- `message.BufWrite`'s frame: the length as 4 little-endian bytes, then the data. -/
def frame (bs : List w8) : List w8 :=
  [BitVec.ofNat 8 bs.length, BitVec.ofNat 8 (bs.length / 256),
   BitVec.ofNat 8 (bs.length / 65536), BitVec.ofNat 8 (bs.length / 16777216)] ++ bs

/-- A sequence of frames. -/
def frames (l : List (List w8)) : List w8 := l.flatMap frame

/-! ## The key-value map (the lab's `Harness.Model`'s, restated: `Model`, `KvInput`, `KvOutput`,
`kv`; as dsv-vr's `VsrModel.kvStep`) -/

/-- A service's model: a state machine whose step relates a state and an input to a next state and
an output (the lab's `Harness.Model.Model`). -/
structure Model where
  State : Type
  Input : Type
  Output : Type
  init : State
  step : State → Input → State → Output → Prop

/-- Inputs of the key-value map (the kit's `In`: a get of `k`, or a put of `v` at `k`). -/
inductive KvInput (K V : Type) where
  | get (k : K)
  | put (k : K) (v : V)
deriving DecidableEq

/-- Outputs of the key-value map (`got none`: the key was never written). -/
inductive KvOutput (V : Type) where
  | got (v : Option V)
  | done
deriving DecidableEq

/-- The key-value map with get and put, from the empty map. -/
def kv (K V : Type) [DecidableEq K] : Model where
  State := K → Option V
  Input := KvInput K V
  Output := KvOutput V
  init := fun _ => none
  step s i s' o := match i with
    | .get k => s' = s ∧ o = .got (s k)
    | .put k v => s' = (fun k' => if k' = k then some v else s k') ∧ o = .done

/-! ## Client commands and the key-value semantics -/

/-- `KeyLen` (`config.CalcConstants`). -/
def keyLen : Nat := 8

/-- A client command as Rabia's client writes it: `"0"+key+value` (a put) or `"1"+key` (a get).
`"0"` is the byte 48, `"1"` the byte 49. -/
def putCmd (k v : GoString) : GoString := (48#8) :: k ++ v
def getCmd (k : GoString) : GoString := (49#8) :: k

/-- The key-value state as the proxy's store holds it (`KVStore`: a missing key reads `""`). -/
abbrev KStore := GoString → Option GoString

/-- `proxy.naiveExecuteCmd`: the new store and the result string. -/
def execCmd (s : KStore) (cmd : GoString) : KStore × GoString :=
  let key := (cmd.drop 1).take keyLen
  let val := cmd.drop (1 + keyLen)
  if cmd.take 1 = [48#8] then
    ((fun k => if k = key then some val else s k), (48#8) :: key ++ [111#8, 107#8])
  else
    (s, (49#8) :: key ++ (s key).getD [])

/-! ## The deployment's configuration (stage 2)

The client node's `New` chooses it (`kit.go`'s `choose`, any value of `math/rand.Intn`) and sends
it to the server nodes (`Conf.encode`, five bytes). `RCfg` mirrors the adapter's `Conf`: `N`, `F`
and the positions of the proxies' batch size, batch timeout and the phase arrays' length in their
lists (`batchSize`, `batchMs`, `blocks`). -/

/-- The adapter's `Conf`. -/
structure RCfg where
  n : Nat
  f : Nat
  batch : Nat
  bms : Nat
  blocks : Nat
deriving DecidableEq, Inhabited

/-- A configuration `choose` can pick (and `decode` accepts). -/
def RCfg.Ok (c : RCfg) : Prop :=
  ((c.n = 3 ∧ c.f = 1) ∨ (c.n = 5 ∧ c.f = 1) ∨ (c.n = 5 ∧ c.f = 2)) ∧
  c.batch < 4 ∧ c.bms < 5 ∧ c.blocks < 4

instance (c : RCfg) : Decidable c.Ok := by unfold RCfg.Ok; infer_instance

/-- The proxies' batch size (`batchSize(Batch)`): 1, 2, 3 or 10 client requests. -/
def RCfg.batchSize (c : RCfg) : Nat := [1, 2, 3, 10].getD c.batch 0
/-- The batch timeout in ms (`batchMs(BatchMs)`). -/
def RCfg.batchMs (c : RCfg) : Nat := [1, 2, 5, 10, 50].getD c.bms 0
/-- The phase arrays' initial length (`blocks(Blocks)`, `Conf.LenBlockArray`). -/
def RCfg.blockLen (c : RCfg) : Nat := [2, 3, 5, 10].getD c.blocks 0

/-- The quorum of a round: `n - f` messages (`Conf.NMinusF`). -/
def RCfg.q (c : RCfg) : Nat := c.n - c.f
/-- `Conf.Majority`. -/
def RCfg.maj (c : RCfg) : Nat := c.n / 2 + 1
/-- `Conf.MajorityPlusF`. -/
def RCfg.mpf (c : RCfg) : Nat := c.n / 2 + c.f + 1
/-- `Conf.FaultyPlusOne`. -/
def RCfg.fp1 (c : RCfg) : Nat := c.f + 1

/-- `Conf.encode`: N, F, Batch, BatchMs, Blocks, one byte each. -/
def RCfg.enc (c : RCfg) : List w8 :=
  [BitVec.ofNat 8 c.n, BitVec.ofNat 8 c.f, BitVec.ofNat 8 c.batch, BitVec.ofNat 8 c.bms,
   BitVec.ofNat 8 c.blocks]

/-- `decode`: the configuration five bytes encode, if `choose` can pick it. -/
def RCfg.dec (b : List w8) : Option RCfg :=
  match b with
  | [n, f, ba, bm, bl] =>
    let c : RCfg := ⟨n.toNat, f.toNat, ba.toNat, bm.toNat, bl.toNat⟩
    if (c.n = 3 ∨ c.n = 5) ∧ 1 ≤ c.f ∧ 2 * c.f < c.n ∧ c.batch < 4 ∧ c.bms < 5 ∧ c.blocks < 4
    then some c else none
  | _ => none

theorem RCfg.dec_enc (c : RCfg) (h : c.Ok) : RCfg.dec c.enc = some c := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := c
  simp only [RCfg.Ok] at h
  obtain ⟨hnf, hb, hm, hl⟩ := h
  have e3 : c3 % 2 ^ 8 = c3 := Nat.mod_eq_of_lt (by omega)
  have e4 : c4 % 2 ^ 8 = c4 := Nat.mod_eq_of_lt (by omega)
  have e5 : c5 % 2 ^ 8 = c5 := Nat.mod_eq_of_lt (by omega)
  rcases hnf with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2 <;>
    simp [RCfg.dec, RCfg.enc, e3, e4, e5, hb, hm, hl]

theorem RCfg.batchSize_le10 (c : RCfg) : c.batchSize ≤ 10 := by
  unfold RCfg.batchSize
  match c.batch with
  | 0 => decide | 1 => decide | 2 => decide | 3 => decide | _ + 4 => simp

theorem RCfg.Ok.batchSize_le {c : RCfg} (h : c.Ok) : 1 ≤ c.batchSize ∧ c.batchSize ≤ 10 := by
  obtain ⟨-, hb, -, -⟩ := h
  unfold RCfg.batchSize
  have : c.batch = 0 ∨ c.batch = 1 ∨ c.batch = 2 ∨ c.batch = 3 := by omega
  rcases this with h | h | h | h <;> simp [h]

/-- What the protocol's safety needs of the numbers: `n ≥ 2f + 1`, `f ≥ 1`. -/
theorem RCfg.Ok.nf {c : RCfg} (h : c.Ok) : 1 ≤ c.f ∧ 2 * c.f + 1 ≤ c.n := by
  unfold RCfg.Ok at h; omega

end Perennial.rabia.model
