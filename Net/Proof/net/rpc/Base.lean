/-
Shared definitions of the proofs of the net/rpc model (`models/net/rpc`, Go 1.27.3's `net/rpc` with
gob and reflection replaced: `codec.go`; phase 5.2 of `notes/dsverify-net-port-plan.md`): the
model's wire format, as pure functions of the bytes, and their pure facts.

**The wire** (`codec.go`'s doc): each gob message of Go's net/rpc (a request or response header, a
body) is one frame, `frameOf p`: `p`'s length in 8 bytes, little-endian, then `p`. A string in a
header is `strEnc s` (its length, 8 bytes, then its bytes). A request header's payload is
`reqHdr seq sm` (the sequence number, then the service method), a response header's
`respHdr seq sm e` (the sequence number, the service method, the error string, `""` for none).
After a header frame comes its body frame: the codec's encoding of the argument or reply (an
empty payload after an error response).

Ported from dsverify-lab's `Harness/Proof/net/rpc/{Proto,WireSpec}.lean` (`348a866`): `frameOf`,
`framesOf` and their facts are dsverify's; `strEnc`, `reqHdr`, `respHdr` replace dsverify's
`msgOf` (its frames held a message with its body; Go's net/rpc sends a header and a body as two
gob messages, the model as two frames).
-/
module

public import Net.GeneratedProof.net.rpc
public import Perennial.Proof.encoding.binary.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

namespace net.rpc

/-! ## The wire format -/

/-- A frame: `p`'s length (8 bytes, little-endian) and `p` (`putFrame`). -/
def frameOf (p : List w8) : List w8 := u64Le (W64 p.length) ++ p

/-- Frames of each payload, in order. -/
def framesOf (ps : List (List w8)) : List w8 := (ps.map frameOf).flatten

/-- A string in a header: its length (8 bytes, little-endian) and its bytes (`putString`). -/
def strEnc (s : GoString) : List w8 := u64Le (W64 s.length) ++ s

/-- A request header's payload (`clientCodec.WriteRequest`): the sequence number and the service
method. -/
def reqHdr (seq : w64) (sm : GoString) : List w8 := u64Le seq ++ strEnc sm

/-- A response header's payload (`serverCodec.WriteResponse`): the sequence number, the service
method and the error string. -/
def respHdr (seq : w64) (sm e : GoString) : List w8 := u64Le seq ++ strEnc sm ++ strEnc e

/-- A request on the wire (`clientCodec.WriteRequest`): its header frame, then its body frame (the
codec's encoding `eb` of the argument). -/
def reqWire (seq : w64) (sm : GoString) (eb : List w8) : List w8 :=
  frameOf (reqHdr seq sm) ++ frameOf eb

/-- A response on the wire (`serverCodec.WriteResponse`): its header frame, then its body frame (the
codec's encoding `eb` of the reply; empty after an error, `e ≠ ""`). -/
def respWire (seq : w64) (sm e : GoString) (eb : List w8) : List w8 :=
  frameOf (respHdr seq sm e) ++ frameOf (if e = [] then eb else [])

/-- The largest frame payload a reader accepts (`maxFrame`, 1 GiB). -/
def maxFrameN : Nat := 2 ^ 30

/-! ## Pure facts -/

theorem frameOf_length (p : List w8) : (frameOf p).length = 8 + p.length := by
  simp [frameOf, u64Le_length]

theorem strEnc_length (s : GoString) : (strEnc s).length = 8 + s.length := by
  simp [strEnc, u64Le_length]

theorem reqWire_length (seq : w64) (sm : GoString) (eb : List w8) :
    (reqWire seq sm eb).length = 8 + (8 + (8 + sm.length)) + (8 + eb.length) := by
  simp [reqWire, frameOf_length, reqHdr, strEnc_length, u64Le_length]

theorem framesOf_nil : framesOf [] = [] := rfl

theorem framesOf_cons (p : List w8) (ps : List (List w8)) :
    framesOf (p :: ps) = frameOf p ++ framesOf ps := by
  simp [framesOf]

theorem framesOf_append (ps qs : List (List w8)) :
    framesOf (ps ++ qs) = framesOf ps ++ framesOf qs := by
  simp [framesOf]

/-- `W64` is injective below `2 ^ 64`. -/
theorem W64_natCast_inj {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : (W64 a : w64) = W64 b) : a = b := by
  have := congrArg BitVec.toNat h
  simp [W64] at this
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

/-- Two frames at the start of a stream agree (payloads shorter than `2 ^ 63`). -/
theorem frameOf_prefix_eq {p p' x y : List w8} (hp : p.length < 2 ^ 63)
    (hp' : p'.length < 2 ^ 63) (h : frameOf p ++ x <+: frameOf p' ++ y) : p = p' := by
  obtain ⟨t, ht⟩ := h
  simp only [frameOf, List.append_assoc] at ht
  obtain ⟨h1, h2⟩ := List.append_inj ht (by simp [u64Le_length])
  have hl : p.length = p'.length :=
    W64_natCast_inj (by omega) (by omega) (u64Le_inj h1)
  exact (List.append_inj h2 hl).1

/-- `strEnc` decodes uniquely (strings shorter than `2 ^ 63`). -/
theorem strEnc_append_inj {s s' : GoString} {r r' : List w8} (hs : s.length < 2 ^ 63)
    (hs' : s'.length < 2 ^ 63) (h : strEnc s ++ r = strEnc s' ++ r') : s = s' ∧ r = r' := by
  simp only [strEnc, List.append_assoc] at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp [u64Le_length])
  have hl : s.length = s'.length := W64_natCast_inj (by omega) (by omega) (u64Le_inj h1)
  exact List.append_inj h2 hl

end net.rpc

end Perennial
