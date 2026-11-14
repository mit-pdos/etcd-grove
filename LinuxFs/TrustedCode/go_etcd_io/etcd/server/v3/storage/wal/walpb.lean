/-
Trusted model of `go.etcd.io/etcd/server/v3/storage/wal/walpb` (namespace of the generated package;
project etcd's part `LinuxFs/`, `LinuxFs/Code/go_etcd_io/etcd/server/v3/storage/wal/walpb.toml`):
`(*Record).Reset`, what the WAL's decoder calls before each `proto.Unmarshal` (`decodeRecord`:
`rec.Reset()`). **Pending the user's review** (a trusted model, 2026-11-14; plan §10 of
`notes/wal-fsext-plan.md`).
-/
module

public import Perennial.Golang.Defn

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial

namespace go_etcd_io.etcd.server.v3.storage.wal.walpb

section code
variable [GooseExts] [GoGlobalContext]

/-- `walpb.Record`'s Go type, by name (the translation's `Record.ty`, which this file, imported by
the translation, cannot name; `Record.ty` unfolds to it). -/
@[reducible] def model.Record : go.GoType :=
  go.GoType.Named go!"go.etcd.io/etcd/server/v3/storage/wal/walpb.Record" []

/-- `(*Record).Reset()` (`record.pb.go`, protoc-gen-go v2):

```go
func (x *Record) Reset() {
	*x = Record{}
	mi := &file_record_proto_msgTypes[0]
	ms := protoimpl.X.MessageStateOf(protoimpl.Pointer(x))
	ms.StoreMessageInfo(mi)
}
```

The model is the first statement, `*x = Record{}`: a store of `Record`'s zero value through `x`
(every field zeroed: `state`, `Type`, `Crc`, `Data`, `unknownFields`, `sizeCache`). Why leaving out
the other two is faithful: `MessageStateOf(x)` is `x`'s first field `state` seen through `unsafe`
(a `*messageState`, no allocation, no check), and `StoreMessageInfo(mi)` is an atomic store of
`mi`, the package's fixed message descriptor of `Record`, into `state`'s message-info cache. That
cache is private to the protobuf runtime: nothing in `walpb` or the WAL reads `state`, and the
runtime reads it only through `ProtoReflect`, which (`record.pb.go`) stores the same `mi` when it
finds the cache `nil` (`if ms.LoadMessageInfo() == nil { ms.StoreMessageInfo(mi) }`) before any
use. So a `Record` whose cache is `nil` (the model's) and one whose cache holds `mi` (Go's) behave
alike under every operation on them; the `proto` specs over a registered message (the trust
boundary, `proto.Unmarshal`'s at `pbRecordC`) take a blank record as the zero value
(`pbRecordC.blank`), the model's result. Go's statement panics on a `nil` `x` (the store's
dereference): so does the model's store. Go example: none needed (no kernel or runtime behavior is
claimed beyond the lazily filled cache, which `record.pb.go`'s `ProtoReflect` shows). -/
noncomputable def Record.Reset.impl : val :=
  λ: "x" <>,
    "x" <-[model.Record] GoZeroVal model.Record #()

end code
end go_etcd_io.etcd.server.v3.storage.wal.walpb

end Perennial
