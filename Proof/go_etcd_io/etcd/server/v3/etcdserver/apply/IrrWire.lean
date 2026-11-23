/-
**The `AuthUserGrantRole` field of an `InternalRaftRequest` on the wire** (protobuf trust-boundary
stage S2, mit-pdos/etcd-grove#37): what protobuf-go v1.36.12's `proto.Unmarshal` into an
`*etcdserverpb.InternalRaftRequest` makes of that one field, as a function of the bytes over the
generic wire format (`Proof/google_golang_org/protobuf/proto/Wire.lean`). Pure and computable:
the request's decoding `apply.irrDecode` (`InvRequest.lean`) takes this field from here and the
rest from an opaque decoder, and `IrrWireVectors.lean` checks it against protobuf-go.

`api/etcdserverpb` at the server pin (proto3): `InternalRaftRequest.auth_user_grant_role` is field
1104 (`raft_internal.proto`), an `AuthUserGrantRoleRequest`, whose `user` 1 and `role` 2 are
`string`s (`rpc.proto`). protobuf-go reads:
- the request's records in order (`unmarshalPointer`); this reader declares only field 1104 (with
  wire type 2) and skips every other record as `protowire.ConsumeFieldValue` would: a known field
  of another number is read by its coder over the same bytes (a varint, a length-delimited value,
  ...) and may only fail where the skip fails or later (a nested message, a string's UTF-8), so
  wherever protobuf-go succeeds this reader does too, and reads the same records of field 1104;
- the field's records merged (`consumeMessageInfo`: the first allocates the message, each one is
  unmarshalled into it), `nil` if there is none;
- a proto3 `string` record (`consumeStringValidateUTF8`): an error unless its bytes are valid UTF-8
  (`utf8.Valid`, `utf8ValidB`), each record checked; the last record wins.
Where protobuf-go fails this reader may succeed (a malformed other field): it claims nothing
there, the opaque part of `irrDecode` failing for it.
-/
module

public import Proof.google_golang_org.protobuf.proto.Wire
public import Proof.unicode.utf8.Valid

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace IrrWire

open Wire

/-- The fields of an `InternalRaftRequest` this reader decodes: `auth_user_grant_role` (1104). -/
def irrUgrSchema : FieldSchema := [(1104, [2])]

/-- `AuthUserGrantRoleRequest` (`rpc.proto`, proto3): 1 `user`, 2 `role` (`string`). -/
def ugrSchema : FieldSchema := [(1, [2]), (2, [2])]

/-- **`proto.Unmarshal` of an `AuthUserGrantRoleRequest` field's occurrences** (merged): `some
none` if there is none (`nil`), `some (some (GetUser(), GetRole()))`, or `none` (an error: an
occurrence does not decode, or a string record is not valid UTF-8). -/
def ugrDecodeRaw (parts : List (List w8)) : Option (Option (List w8 × List w8)) :=
  if parts = [] then some none
  else
    match decodeMerged ugrSchema parts with
    | none => none
    | some (ks, _) =>
      if (allLen ks 1).all utf8ValidB && (allLen ks 2).all utf8ValidB then
        some (some ((lastLen ks 1).getD [], (lastLen ks 2).getD []))
      else none

/-- **The `AuthUserGrantRole` field of `proto.Unmarshal` into an `InternalRaftRequest`**: `some
none` if it is `nil`, `some (some (user, role))`, or `none` (an error; see the file header for
what `some` claims). -/
def irrUgrDecodeRaw (bs : List w8) : Option (Option (List w8 × List w8)) :=
  match decode irrUgrSchema bs with
  | none => none
  | some (ks, _) => ugrDecodeRaw (allLen ks 1104)

theorem utf8ValidB_nil : utf8ValidB [] = true := rfl

theorem getLast?_mem {α : Type} {l : List α} {a : α} (h : l.getLast? = some a) : a ∈ l :=
  List.mem_of_getLast? h

/-- **A decoded role is valid UTF-8.** -/
theorem irrUgrDecodeRaw_utf8 {bs : List w8} {ur : List w8 × List w8}
    (h : irrUgrDecodeRaw bs = some (some ur)) : utf8ValidB ur.2 = true := by
  unfold irrUgrDecodeRaw at h
  split at h
  · simp at h
  · rename_i ks _ _
    unfold ugrDecodeRaw at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i ks2 _ _
        split at h
        · rename_i hv
          simp only [Option.some.injEq] at h
          subst h
          simp only [Bool.and_eq_true, List.all_eq_true] at hv
          cases hl : lastLen ks2 2 with
          | none => rfl
          | some r =>
            simp only [Option.getD_some]
            apply hv.2
            unfold lastLen at hl
            unfold allLen
            exact getLast?_mem hl
        · simp at h

end IrrWire
end EtcdGrove
end Perennial
