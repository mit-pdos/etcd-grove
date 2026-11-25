/- Lean-first (no Rocq counterpart).

# `net/rpcdriver`: the bytes of its net/rpc values

The driver's generated codec (`examples/net/rpcdriver/rpc_gen.go`, by `models/net/rpc/rpcgen.py`)
as pure functions of the values it encodes: the request `service.Args` and the reply
`service.Reply` (as the kits' `RpcWire.lean`).

A top-level value is its type's name (`rpcPutTag`: the name's length, 8 bytes little-endian, and
its bytes) and the value. A `uint64` is 8 bytes little-endian; a `[]byte` its count and each byte as
a `uint8`, itself 8 bytes (`rpcEnc_t5`, `rpcEnc_t6`); a string its length and its bytes. A struct is
the byte 1, then per field a byte 1 and the field's value if the field is sent (not its zero
value: gob's rule), else a byte 0.
-/
module

public import Perennial.Std.Word.LittleEndian
public import Perennial.Std.ByteString

@[expose] public section

noncomputable section

namespace Perennial

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.wire

/-- A string: its length and its bytes (`rpcEnc_t7`; also `rpcPutTag`). -/
def encStr (s : GoString) : List w8 := u64Le (W64 s.length) ++ s

/-- A `[]byte` (`rpcEnc_t5`): its count, then each byte as a `uint8` (8 bytes, `rpcEnc_t6`). -/
def encBytes (bs : List w8) : List w8 :=
  u64Le (W64 bs.length) ++ (bs.map (fun b => u64Le (W64 (uint.Z b)))).flatten

/-- A struct field: sent (`1` and its value) or not (`0`). -/
def fld (sent : Bool) (body : List w8) : List w8 := if sent then W8 1 :: body else [W8 0]

/-- A `uint64` field (`rpcEnc_t4`, sent unless zero). -/
def fU64 (x : w64) : List w8 := fld (decide (x ≠ W64 0)) (u64Le x)

/-- A `[]byte` field (sent unless empty). -/
def fBytes (bs : List w8) : List w8 := fld (decide (bs ≠ [])) (encBytes bs)

/-- A string field (sent unless empty). -/
def fStr (s : GoString) : List w8 := fld (decide (s ≠ [])) (encStr s)

/-- A struct of the fields `fs`. -/
def strct (fs : List (List w8)) : List w8 := W8 1 :: fs.flatten

/-- A top-level value of the type named `t`. -/
def tagged (t : GoString) (body : List w8) : List w8 := encStr t ++ body

/-- The type names (`rpcPutTag`'s arguments). -/
def tArgs : GoString := go!"github.com/mit-pdos/etcd-grove/examples/net/rpcdriver/service.Args"
def tReply : GoString := go!"github.com/mit-pdos/etcd-grove/examples/net/rpcdriver/service.Reply"

/-- `service.Args{ID: id, Data: data, Fail: fail}` (`rpcEncode` of a `*service.Args`). -/
def encArgs (id : w64) (data : List w8) (fail : GoString) : List w8 :=
  tagged tArgs (strct [fU64 id, fBytes data, fStr fail])

/-- `service.Reply{ID: id, Data: data, Runs: runs}` (`rpcEncode` of a `*service.Reply`). -/
def encReply (id : w64) (data : List w8) (runs : w64) : List w8 :=
  tagged tReply (strct [fU64 id, fBytes data, fU64 runs])

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.wire

end Perennial
