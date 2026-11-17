# auth-schema-srv A3: Draft (Marshal of `authpb.User`/`Role`; size caches out of `↦□`)

**Applied 2026-11-17** (decisions §7 accepted by etcd-grove-03 after the attack, `notes/axiom-review/auth-a3-marshal.md`; MINORs m1-m3 folded in). 2026-11-17. Scope: `notes/auth-schema-srv-scope.md` §3 (A3), Q3 (Marshal axioms mirroring the Unmarshal
ones), Q4 (follow-up (a)). Status: **texts for an independent attack; no axiom file yet.** Nothing in
`Buckets.lean` is changed yet; the restated predicates are elaborated in `Scratch/A3Preds.lean`
(untracked; `lean-check -a`: 0 errors), the two new specs are `Spec/.../proto/MarshalUser.lean` and
`MarshalRole.lean` (elaborated, 0 errors; no `Proof/` file). Go evidence:
`examples/authpbmarshal/marshal_test.go` (10 tests, pass with `-race`, go1.27.3, protobuf-go v1.36.12,
the fork's authpb at the etcd pin 8c28a4296f).

## 1. What changes, in one paragraph

protobuf-go's `Marshal` writes, atomically, the size cache of the top message **and of every nested
message** (`internal/impl/encode.go:63-125`), and `ProtoReflect` (any reflective use: `String()`,
protojson) writes a message's `state` once, atomically (`TestStateWrites`). Today `userOptsIs`
(the `Options` of a user), `ownPermW` (a request's permission) and `ownPermS` (a stored role's
permission) hold the whole nested struct `↦□`, `state` and `sizeCache` included: a Marshal spec over
them would claim a write to a read-only cell. The restatement holds the nested message **field by
field**: its wire fields `↦□` as before, its size cache in an invariant (any value: the precedent
`txn.putRequestIs`, restart1's `Requests.lean`), its `state` not at all. The two new axioms then
state `proto.Marshal` of a `*authpb.User` over `ownUser` (valid UTF-8 roles) and of a `*authpb.Role`
over `ownRole`, returning `userEncode x` / `roleEncode x`, the encodings `UnmarshalUser`/`UnmarshalRole`
decode.

## 2. The texts

### 2.1 New vocabulary (Buckets.lean)

```lean
/-- The namespace of the invariants holding the size caches of the auth messages' nested messages
(`userOptsIs`, `ownPermW`, `ownPermS`). -/
def pbSizeCacheN : Namespace := nroot .@ "authpb.sizeCache"
```

### 2.2 Restated (Buckets.lean; trusted: the axioms below and the request models mention them)

`ownUser`, `ownRole`, `ownUserX`, `ownRoleX`, `ownPermX`, `userOptsAt` keep their texts. Lemmas that
change proof only: `ownPermS_W` (per-field), `ownPermX_persist`/`ownRoleX_persist` (`|==>` → `|={E}=>`:
the invariant is allocated), `ownUserX_persist` unchanged.

```lean
/-- The `*authpb.UserAddOptions` `o` holds `NoPassword = b` and the rest `ou` of a user record's
`Options` (`UserRec.optsUF`): nil (`GetNoPassword()` is false; `ou = none`), or a message whose wire
fields are read-only (`NoPassword`, and its unknown fields, a read-only slice holding the bytes `u`,
`ou = some u`) and whose size cache is in an invariant (`pbSizeCacheN`, any value): protobuf-go's
`Marshal` of a message holding it (a `User`, `proto.MarshalUser`; a request, `proto.MarshalIRR`, the
gRPC send) stores it, atomically, and concurrent Marshals of messages sharing it store the same value
(auth-schema-srv A3, 2026-11-17: until then the whole struct was `↦□`, the cache with it; Go tests
`TestMarshalWritesNestedSizeCache`, `TestConcurrentSharedNested`). Its `state` (protobuf-go's message
info, which `ProtoReflect` stores once, atomically, on any reflective use, `String()` included:
`TestStateWrites`) is not held: no spec reads it, and Marshal and Unmarshal of the parent never touch a
nested message's. -/
def userOptsIs (o : Loc) (b : Bool) (ou : Option GoString) : IProp GF :=
  iprop(⌜o = null ∧ b = false ∧ ou = none⌝ ∨
    (⌜o ≠ null⌝ ∗ ∃ (uf : GoSlice) (u : GoString),
      ⌜ou = some u⌝ ∗
      structFieldRef authpb.UserAddOptions go!"NoPassword" o ↦□ b ∗
      structFieldRef authpb.UserAddOptions go!"unknownFields" o ↦□ uf ∗ uf ↦*□ u ∗
      inv pbSizeCacheN (∃ sc : w32, structFieldRef authpb.UserAddOptions go!"sizeCache" o ↦ sc)))

/-- The `*authpb.Permission` at `p` (not nil) holds the wire permission `w`, whose key fits a Go slice
with room for one more byte (`NewBytesAffinePoint` appends `"\x00"` to it: a key of `2^63 - 1` bytes
cannot be unmarshalled; the auth plan's S2): its wire fields read-only, its size cache in an
invariant and its `state` not held, as `userOptsIs` (A3). The permission of a request
(`roleGrantPermissionReqIs`): its unknown fields are free (a client's newer fields; etcd never stores
this message, `ownPermS`). -/
def ownPermW (p : Loc) (w : PermW) : IProp GF :=
  iprop(⌜p ≠ null ∧ w.key.length < 2 ^ 63 - 1⌝ ∗ ∃ (k re uf : GoSlice),
    structFieldRef authpb.Permission go!"PermType" p ↦□ w.ty ∗
    structFieldRef authpb.Permission go!"Key" p ↦□ k ∗
    structFieldRef authpb.Permission go!"RangeEnd" p ↦□ re ∗
    structFieldRef authpb.Permission go!"unknownFields" p ↦□ uf ∗
    inv pbSizeCacheN (∃ sc : w32, structFieldRef authpb.Permission go!"sizeCache" p ↦ sc) ∗
    k ↦*□ w.key ∗ re ↦*□ w.rangeEnd)

/-- **A stored role's permission** `*authpb.Permission` at `p` (not nil): as `ownPermW`, and no unknown
fields (`unknownFields` nil, as `ownRole`'s own: protobuf-go's `Marshal` copies them into the role's
encoding unchecked, so garbage there makes the next `GetRole` panic; the review of auth-schema-fix,
MAJ-1, Go test `zz_review_garbage_test.go`). etcd builds every permission it stores fresh
(`RoleGrantPermission`'s `newPerm`, store.go) or decodes it from a stored role (`proto.Unmarshal` of a
`roleEncode` leaves it nil). Its size cache in an invariant (`proto.MarshalRole` stores it; a
permission may be shared by two roles, or twice by one), its `state` not held (A3). -/
def ownPermS (p : Loc) (w : PermW) : IProp GF :=
  iprop(⌜p ≠ null ∧ w.key.length < 2 ^ 63 - 1⌝ ∗ ∃ (k re : GoSlice),
    structFieldRef authpb.Permission go!"PermType" p ↦□ w.ty ∗
    structFieldRef authpb.Permission go!"Key" p ↦□ k ∗
    structFieldRef authpb.Permission go!"RangeEnd" p ↦□ re ∗
    structFieldRef authpb.Permission go!"unknownFields" p ↦□ slice.nil ∗
    inv pbSizeCacheN (∃ sc : w32, structFieldRef authpb.Permission go!"sizeCache" p ↦ sc) ∗
    k ↦*□ w.key ∗ re ↦*□ w.rangeEnd)
```

### 2.3 New axioms (+2)

The exact specs with their docstrings: `Spec/google_golang_org/protobuf/proto/MarshalUser.lean`
(`proto.MarshalUser.spec`) and `MarshalRole.lean` (`proto.MarshalRole.spec`). In short:

```lean
abbrev proto.MarshalUser.spec : Prop :=
  ∀ (p : Loc) (x : auth.UserRec),
  (∀ r ∈ x.roles, utf8Valid r) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ auth.ownUser p x }}
    (App (Val (@! proto.Marshal))
      (Val #(interface.mkOk (go.GoType.PointerType authpb.User.ty) #p)))
  {{ (d : GoSlice), RET (PairV #d #(GoInterface.nil));
      auth.ownUser p x ∗ d ↦* auth.userEncode x ∗ ownSliceCap w8 d (DFrac.own 1) }}

abbrev proto.MarshalRole.spec : Prop :=
  ∀ (p : Loc) (x : auth.RoleRec),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ auth.ownRole p x }}
    (App (Val (@! proto.Marshal))
      (Val #(interface.mkOk (go.GoType.PointerType authpb.Role.ty) #p)))
  {{ (d : GoSlice), RET (PairV #d #(GoInterface.nil));
      auth.ownRole p x ∗ d ↦* auth.roleEncode x ∗ ownSliceCap w8 d (DFrac.own 1) }}
```

Axiom files (after the attack): `Proof/google_golang_org/protobuf/proto/Marshal{User,Role}.lean`,
`axiom proto.MarshalUser.wp_proof : proto.MarshalUser.spec (GF := GF) (hG := hG)` (as
`UnmarshalUser.lean`).

### 2.4 Docstring edit (trusted text, wording only): `MarshalIRR.lean`'s last paragraph

Old: "The size caches protobuf-go stores in the messages (atomically) are outside the model:
`internalRaftRequestIs` and the KV requests' predicates do not own them."
New: "The size caches protobuf-go stores in the messages (atomically) are outside the model:
`internalRaftRequestIs` and the KV requests' predicates do not own them; except a user addition's
`Options` and a permission grant's `Permission`, whose caches are in invariants (`auth.userOptsIs`,
`auth.ownPermW`; auth-schema-srv A3), which this call stores."

## 3. Trusted texts whose meaning moves (text unchanged)

Through the three definitions:
- `proto.UnmarshalUser.wp_proof` (post `ownUserX` → `userOptsIs`): the decoded `Options` now comes with
  its cache in an invariant, no `state`. True of Go (a fresh message the decoder allocates).
- `proto.UnmarshalRole.wp_proof`: **no change** (`ownRoleX` holds `ownPermX`, owned, unchanged).
- `proto.MarshalIRR.wp_proof` (pre `internalRaftRequestIs` → `userOptsAt`, `roleGrantPermissionReqIs` →
  `ownPermW`) and `pbutil.MustUnmarshalMessage.wp_proof` (post, the same): the request's `Options`/`Perm`
  caches in invariants. MarshalIRR's footprint now holds the cells it writes there (more honest).
- The gRPC models of `AuthUserAddRequest`/`AuthRoleGrantPermissionRequest` (`PerTypeAuth.lean`'s
  instances under the `pb*_reg` axioms; `send`/`recv` hold `userOptsAt`/`ownPermW`).
- **Exported statement**: `v3rpc.userAdd_end_to_end_on` (`api/v3rpc/Results.lean:805`, premise
  `auth.userOptsAt o b`). Incomparable to the old premise (per-field `↦□` + an invariant vs the whole
  struct `↦□`); both follow from a freshly allocated message, which is what gRPC's decoder gives.
- `auth.authBatchTxLk(R)` (hD22's text, internal until A7) via `ownUser`/`ownRole`: no text change.

## 4. Go evidence (`examples/authpbmarshal/marshal_test.go`)

| Claim | Test |
|---|---|
| Marshal writes the nested caches (the old `↦□` was false) | `TestMarshalWritesNestedSizeCache` |
| Marshal sets the top `state`, never a nested one; `String()` sets a nested one | `TestStateWrites` |
| Any value in any cache (top or nested, incl. negative, 1, MaxInt32) gives the same bytes | `TestStaleSizeCacheIgnored` |
| Encoding a function of the record: nil vs empty byte fields/lists/unknown fields, fresh vs decoded vs already marshaled, 100 calls | `TestDeterministicRecord` |
| nil vs empty `Options` differ; decode back to `none`/`some []`; empty role kept | `TestNilVsEmptyOptions` |
| `Options`' unknown fields verbatim both ways (either `NoPassword`); top unknown decode nil | `TestOptionsUnknownRoundTrip` |
| Permissions (types 0,1,2,7,-1) round-trip, in order, no unknown fields | `TestRoleRoundTrip` |
| invalid UTF-8 role ⇒ error (the premise) | `TestInvalidUTF8Role` |
| Fresh result (no aliasing) | `TestFreshResult` |
| Concurrent Marshals of users sharing an `Options` and roles sharing a permission (twice in one), with concurrent readers: `-race` silent, all results right | `TestConcurrentSharedNested` |

Run: `cd examples && GOWORK=off GOTOOLCHAIN=go1.27.3 go test -race -count=1 ./authpbmarshal/`.

## 5. The axiom skill's families, checked by the author (the attack is to be independent)

- *False pure fact*: the result is `userEncode x`; `userEncode` is opaque, constrained only by
  `UnmarshalUser` (decode gives `x` back). Needs the real encoding injective on the records `ownUser`
  can hold: `GoString` has no nil/empty distinction; `Options` none/some differ (test 5); `(true, u)` vs
  `(false, 0x08 0x01 ++ u)` excluded by `ufWire userOptsSchema` (field 1 varint is a known field);
  roles keep order and empties. Roles: permission type any `w32` (sign-extended varint, decoded back).
- *Missing premise*: UTF-8 roles (the only string field). A nil permission (Marshal refuses it):
  excluded by `ownPermS`'s `p ≠ null`. Size: the top size only sizes the buffer; a wrapped top size
  needs a `2^63`-byte encoding (out-of-memory exit, never a wrong result; the model's allocation
  idealization); nested sizes are bounded by two or three byte slices each (no wrap). No premise added
  (as `proto.Marshal` of a `KeyValue`).
- *Too much ownership*: top message owned (both writes it); nested caches in invariants; the read-only
  fields are only read by Marshal; the result fresh (test 9).
- *Too-strong persistent fact*: the fix itself (`sizeCache`, `state` out of `↦□`). Remaining `↦□`
  fields: only `Reset` (a whole-struct store, which the read-only fields exclude) and `Unmarshal` into
  that message (needs it owned) write them.
- *Interacting triples*: Marshal then Unmarshal round-trips (tests 4-7); concurrent Marshals over shared
  nested messages (test 10; a concurrent Size pass stores the same value, the content being
  read-only). The invariant allows any value at any time, but only protobuf-go writes the field (it is
  unexported; generated code writes it only in `Reset`).
- *Package init*: as the Unmarshal axioms (`proto`'s `isPkgInit`; authpb is initialized in any program
  that can name its types).
- *Cross-world entailment* (branch soundness-1117's check): **none**. The restated predicates are
  definitions with no law to a pure equation; the axioms' `userEncode x` is per-run (a post), of a
  pure record, not an entailment from persistent cells to an equation of an opaque function of a
  pointer.

## 6. Findings (MINOR, no refutation)

- **m1 (UnmarshalUser, existing):** for records no message can hold (a role not valid UTF-8; or
  `noPassword = true ∧ optsUF = none`), the axiom's post is unsatisfiable by Go (`ownUserX` is then
  false, or holds non-UTF-8 strings the decoder never yields): the axiom has no model at those
  records. Not exploitable: no law or axiom produces `userEncode x` for such `x` (`MarshalUser` needs
  `ownUser` and UTF-8 roles; the bucket states carry `rolesUtf8`). Recommend: leave; or later a
  `UserRec` well-formedness premise on `UnmarshalUser`.
- **m2 (MarshalIRR, existing):** the other nested request messages' caches remain "outside the model",
  and `ownPermW`'s unknown-field bytes (which MarshalIRR copies) are not held. Same class as Q4; not
  this stage.

## 7. Decisions requested

1. Accept the three restatements (§2.2) with `state` **not held** (recommended; alternative: `state` in
   the same invariant, `∃ st sc`, no gain: nothing reads it) and one namespace `pbSizeCacheN`.
2. Accept the two axioms (§2.3) after an independent attack (axiom skill), with the UTF-8 premise and
   no size premise.
3. Accept the MarshalIRR docstring edit (§2.4) and the exported `userAdd_end_to_end_on`'s moved meaning
   (§3).

After the go (A3's Freeze): apply §2.2 in `Buckets.lean` (+ `pbSizeCacheN`), adapt the constructors
(`PerTypeAuth` `treeWp_userOpts`/`permWTree`: `inv_alloc` in their fupd; `RoleGrantPermission`'s
`newPerm`; `ownPermX_persist`/`ownRoleX_persist` and their callers to fupd) and the readers (per-field
loads: `CheckPassword`, `Authenticate`, `PermSorter`, `getMergedPerms`, `RoleGet`, `Reads`, client
`InvAuthConn`/`authClient__*`), the axiom files, `etc/tcb-baseline.txt` +2 (reached at A5), the
collections, interfaces. Estimate 300-500 lines.
