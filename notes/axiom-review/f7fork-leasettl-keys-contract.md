# `EtcdServer.leaseTimeToLive`: the owned-keys conjunct (delta review, 2026-11-26)

**Verdict: SOUND** (the delta). One docstring nit (a line range off by one), no change to the statement.

Axiom `EtcdServer.leaseTimeToLive.wp_proof : EtcdServer.leaseTimeToLive.spec`, spec file
`Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__leaseTimeToLive.lean`, branch `etcd-safe-f7-fork/2026-11-26`.
Delta reviewed: `git diff c5f0a53378 487d74f4ae` of that file. The only change to the statement is the conjunct of the
success arm

```lean
(∃ kbs : List GoSlice, w.Keys' ↦* kbs ∗
  [∗list] kb ∈ kbs, ∃ k : List w8, kb ↦* k ∗ ⌜sint.Z kb.len < 2 ^ 63 - 1⌝)
```

full ownership of the returned response's `Keys` slice (its first `len` cells) and of every key's bytes (its first
`len` cells; no capacity is claimed), each key shorter than `2^63 - 1`. The rest of the statement was reviewed before
and is considered here only where it meets the new conjunct.

Go code: etcd fork `/shared/etcd-fork-ttlkeys` at `d26dd5da6`; google.golang.org/protobuf `v1.36.12`
(`server/go.mod:42`), source `/root/go/pkg/mod/google.golang.org/protobuf@v1.36.12` (below `$PB`); toolchain go1.27.3
(`etc/goose.py`'s `GO_TOOLCHAIN`).

## Claims

1. The `Keys` slice header's cells (`len` many) are the caller's alone.
2. Each key's bytes are the caller's alone: no other goroutine, no buffer someone keeps, no other key of the same
   response (except zero-length ones, which own nothing) shares them.
3. Each key's length is below `2^63 - 1`.

## 1. The follower path: protobuf-go copies every key (the aliasing question)

`leaseTimeToLive`'s forwarded branch returns `resp.LeaseTimeToLiveResponse` of `leasehttp.TimeToLiveHTTP`
(`server/etcdserver/v3_server.go:683-685`), which reads the body with `readResponse` (`io.ReadAll` of a `LimitReader`
over `resp.Body`, `server/lease/leasehttp/http.go:287-299`: a fresh buffer `b`), and decodes it with
`proto.Unmarshal(b, lresp)` into a fresh `&leasepb.LeaseInternalResponse{}` (`http.go:269-270`), returning `lresp`
(`http.go:276`).

- The messages are protoc-gen-go v2 (`api/etcdserverpb/rpc.pb.go:1-5`, `protoimpl.MessageState`; same for
  `server/lease/leasepb/lease.pb.go`), so `proto.Unmarshal` takes the fast path: `$PB/proto/decode.go:101-122` builds
  the `protoiface.UnmarshalInput` and calls `methods.Unmarshal`. The flags it may set are `UnmarshalDiscardUnknown`,
  `UnmarshalCheckRequired`, `UnmarshalNoLazyDecoding` (`decode.go:110,116,119`); **never `UnmarshalAliasBuffer`**.
- `Keys` is `[][]byte` with tag `bytes,5,rep` (`rpc.pb.go:2957`), proto3, so its coder is `coderBytesSlice`
  (`$PB/internal/impl/codec_tables.go:117-122`), whose unmarshal is `consumeBytesSlice`
  (`$PB/internal/impl/codec_gen.go:5568-5580`):

  ```go
  v, n := protowire.ConsumeBytes(b)          // v is a sub-slice of the buffer
  ...
  *sp = append(*sp, append(emptyBuf[:], v...)) // :5577, a copy
  ```

  `emptyBuf` is `var emptyBuf [0]byte` (`codec_gen.go:5703`): a non-empty key is a fresh array (`append` to a
  cap-0 slice allocates); an empty key is `emptyBuf[:]`, length 0, **capacity 0**, non-nil. Every empty key of every
  decoded message shares that pointer, but a length-0, capacity-0 slice gives access to no byte. In the model this is
  free ownership: `ownSlice` of `[]` at a non-null pointer is `typedPointsto ptr (array.mk 0 [])`, which `array_empty`
  (Perennial `Golang/Theory/Array.lean:109`) proves from `ptr ≠ null` alone, so sharing it is consistent.
- `consumeBytesSlice` does not consult `AliasBuffer()` at all (`$PB/internal/impl/decode.go:46`; the only reader of
  the flag is lazy extension decoding, `lazy.go:196-201`, `codec_extension.go:152`). So even with aliasing permitted
  the keys are copied (test 1, `alias=true`). No field of `rpc.proto`/`lease.proto` is `[lazy = true]`, and the
  lazy path concerns extensions only.
- The outer `[][]byte` grows by `append` from `nil` in the fresh message: a fresh array.

Hence a decoded key never aliases `b`, and whether `b` (or the transport's own buffers, which `io.ReadAll` copies out
of) is retained or reused is irrelevant. The rest of `lresp` (the wrapper, its `MessageState`, which holds only a
`*MessageInfo`) is dropped when `TimeToLiveHTTP` returns; nothing stores `lresp` or `resp`
(`http.go:224-277`; `v3_server.go:672-696`). Earlier iterations of the retry loop return nothing.

## 2. The leader path: fresh copies, or nil

`v3_server.go:651-659`: `resp` is a fresh literal; with `r.Keys`, `ks := le.Keys()` (a `[]string`,
`server/lease/lease.go:106`), `kbs := make([][]byte, len(ks))` (fresh) and `kbs[i] = []byte(ks[i])` (a copy of an
immutable string: fresh, or, for `""`, a length-0 slice, possibly at `runtime.zerobase`, which owns nothing, as
above). Without `r.Keys`, `resp.Keys` is the zero value `nil`: `ownSlice_nil` gives `nil ↦* []` (Perennial
`Golang/Theory/Slice.lean:118`). When `len(ks) = 0` the slice is a non-nil length-0 slice, again trivial. The lessor
keeps only its strings; nothing the leader path built is stored anywhere (the `Demoted` check returns an error and
drops `resp`).

On a follower with `r.Keys` false, the leader's handler leaves `Keys` unset (`http.go:137-143`), and the decode leaves
it `nil` (test 3).

## 3. No goroutine keeps the response

Leader: `resp` is local and returned. Follower: as in 1; the HTTP client's goroutines (the transport's read/write
loops) hold the connection's buffers, never `b` (fresh from `io.ReadAll`) nor the decoded message. The request `r`
(`r ↦{dq} v`, the only caller memory in the pre) has no slice field (`LeaseTimeToLiveRequest`: `ID`, `Keys bool`),
and the persistent/invariant parts of the pre (`isServerReqM`, `srvLessorRd`, `lessorRdPool`, ...) cannot own
memory that was allocated during the call. `w.Header' ↦ hv` and `resp ↦ w` are other objects (a `*ResponseHeader`, the
struct), disjoint from the `[][]byte` and `[]byte` arrays.

## 4. The length bound

A Go slice's length is at most `maxAlloc` (`2^48` on amd64), far below `2^63 - 1`. More concretely: on a follower the
whole body is at most `maxLeaseHTTPResponseSize = 100 MiB` (`http.go:285,293-296`, a longer body is an error); on the
leader a key is a key of the lessor, put by a request of bounded size. True.

## 5. Other attacks tried

- *Two handles to one key*: the post's `[∗list]` would let a client prove two keys disjoint; they are, except
  zero-length ones, whose ownership is empty (above). No contradiction from separation.
- *Ownership plus the persistent `□ (leaseTTLRow … )` part*: it is about `w.GrantedTTL'`, a pure value; unrelated.
- *A malicious or custom peer transport* (`s.peerRt`), or a server at the peer URL other than etcd's handler
  (`leasePeersOk` restricts only the 200 reply's shape): whatever bytes arrive, the decode copies them, so the conjunct
  holds for any reply that decodes (test 2 uses a transport that keeps and later overwrites its body).
- *Panic of a client using the ownership*: writing the keys (as `checkLeaseTimeToLiveKeys` may only read them) is safe
  in Go: test 2 and test 3 write every decoded key and observe no effect on the body or the lessor.

Not tried: a Lean counterexample (no gap found to build one on); the gRPC marshaling after `LeaseTimeToLive` returns
(outside this axiom: the caller passes the ownership on).

## Tests

`notes/axiom-review/f7fork-leasettl-keys-gotest/keys_alias_test.go`, run in a copy of the fork
(`cp` to `server/lease/leasehttp/`, `GOTOOLCHAIN=go1.27.3 go test -count=1 -run TestF7forkKeys -v ./lease/leasehttp/`):

1. `TestF7forkKeysUnmarshalNoAlias`: decodes a reply with keys `"z/lease", "", "a/other-key", ""` by `proto.Unmarshal`
   and, separately, by the message's `ProtoMethods().Unmarshal` with `UnmarshalAliasBuffer` set; checks with `unsafe`
   that no key's `[ptr, ptr+cap)` overlaps the buffer, that empty keys have cap 0, and that overwriting the buffer
   changes no key.
2. `TestF7forkKeysTimeToLiveHTTPRetainedBody`: `TimeToLiveHTTP` over a `RoundTripper` whose body reads a buffer the
   test keeps; after the call, no key overlaps it, zeroing it changes no key, writing every key leaves it unchanged.
3. `TestF7forkKeysRealHandler`: the real leader handler (`NewHandler` over a real lessor with keys `foo`, `""`, `bar`
   attached): two replies share no key memory; writing the first reply's keys does not reach the lessor (a third reply
   is unchanged); `keys=false` gives `Keys == nil`.

Output (go1.27.3):

```
=== RUN   TestF7forkKeysUnmarshalNoAlias
    keys_alias_test.go:76: alias=false key 0: len 7 cap 8 nil=false
    keys_alias_test.go:76: alias=false key 1: len 0 cap 0 nil=false
    keys_alias_test.go:76: alias=false key 2: len 11 cap 16 nil=false
    keys_alias_test.go:76: alias=false key 3: len 0 cap 0 nil=false
    keys_alias_test.go:76: alias=true key 0: len 7 cap 8 nil=false
    keys_alias_test.go:76: alias=true key 1: len 0 cap 0 nil=false
    keys_alias_test.go:76: alias=true key 2: len 11 cap 16 nil=false
    keys_alias_test.go:76: alias=true key 3: len 0 cap 0 nil=false
--- PASS: TestF7forkKeysUnmarshalNoAlias (0.00s)
=== RUN   TestF7forkKeysTimeToLiveHTTPRetainedBody
--- PASS: TestF7forkKeysTimeToLiveHTTPRetainedBody (0.00s)
=== RUN   TestF7forkKeysRealHandler
    keys_alias_test.go:180: keys=true: ["bar" "foo" ""]
    keys_alias_test.go:188: keys=false: Keys == nil
--- PASS: TestF7forkKeysRealHandler (0.02s)
PASS
ok  	go.etcd.io/etcd/server/v3/lease/leasehttp	0.032s
```

## Nit (docstring only)

The docstring cites the follower's decode as `http.go:268-271`; at `d26dd5da6` it is `http.go:269-271` (`lresp :=`
at 269, `proto.Unmarshal` at 270). It could also say that an empty key is `emptyBuf[:]` (cap 0, shared, owns
nothing), the one case where two returned keys share a pointer. Suggested text, replacing
"`(`http.go:268-271`), whose\nrepeated `bytes` field protobuf-go copies out of the body (`consumeBytesSlice`, `internal/impl/codec_gen.go:5577`:\n`append(emptyBuf[:], v...)`;":

> (`http.go:269-271`), whose repeated `bytes` field protobuf-go copies out of the body (`consumeBytesSlice`,
> `internal/impl/codec_gen.go:5577`: `append(emptyBuf[:], v...)`, whatever the `AliasBuffer` flag, which
> `proto.Unmarshal` never sets; an empty key is `emptyBuf[:]`, of capacity 0, owning nothing;
