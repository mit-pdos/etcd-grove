# grpc-codec-alloc-before-size-check

- **Finding**: `issues/grpc-codec-alloc-before-size-check.md`
- **Target**: grpc/grpc-go, `master` (not one of the skill's etcd-io targets: drafted by hand in the skill's shape,
  with grpc-go's own rules where they differ, below)
- **Branch**: `fix/grpc-codec-alloc-before-size-check` in `~/etcd-fixes/grpc-codec-alloc-before-size-check`
  (worktree of `~/grpc-go`, cloned over HTTPS, remote `upstream` grpc/grpc-go; no fork, no `origin`), two signed-off
  commits: 87decb761 (`encoding/proto: test marshaling a message too large to allocate`) adds the tests, which panic
  there; b3a700339 (`encoding/proto: check the message size before allocating`) is the fix.
- **Base**: upstream `master` bc90736a6fadc41582f9a23fb955bb66088f1bb8 (2026-10-29, `v1.86.0-dev-54`). The code is
  as in v1.84.0, the version the finding was found in (`encoding/proto/proto.go:74`, `pool.Get(size)`, the same line).
- **State**: draft. Nothing pushed, filed or commented.

## Before filing: a crash, which grpc-go routes to its CVE process

grpc-go's bug template says: "if you are reporting is a potential security vulnerability or a crash, please follow
our CVE process at https://github.com/grpc/proposal/blob/master/P4-grpc-cve-process.md instead of filing an issue
here." This is a crash (a panic, not recovered, that ends the process). On the client it is self-inflicted (the
client builds the request). On a server, any handler whose reply a remote client can make encode above 2^48 bytes
(a reply that repeats shared submessages) lets that client crash the server, which is an application's exposure
through grpc. So the user should decide between a public issue (these drafts) and a private report under P4 (the
same text works as the report; the PR would then wait for the maintainers). The etcd side
(`issues/etcd-txn-keysonly-reply-alloc-panic.md`) is on hold by the user's decision; the drafts describe the grpc bug
generically and say nothing of how a server's reply gets that large. The issue ends with the skill's disclosure,
"Found while formally verifying etcd. ...": with the etcd side on hold, consider dropping its first sentence when
filing (it names etcd, though nothing about the member crash).

## grpc-go's rules (CONTRIBUTING.md, `.github/`)

- **CLA, not DCO**: the CNCF Contributor License Agreement (Linux Foundation EasyCLA), signed on the first PR from a
  link the bot posts. grpc-go does not ask for `Signed-off-by` (1 of the last 50 commits has one); the commits have
  it (`git commit -s`, as asked), which is harmless. No AI trailer in the commits.
- **Generative AI policy**: all GitHub interactions authored by a human (AI only as directed writing assistance); the
  author owns and understands every line; the Linux Foundation Generative AI Policy applies. The disclosures at the
  ends of the issue and the PR are compatible with it; the user posts everything.
- **PR description**: becomes the squash-merge commit message; title starts with the component
  (`encoding/proto:`); `Fixes #<issue>` on the first line; ends with `RELEASE NOTES:` (one bullet, a sentence a user
  understands). So `pr.md` has `Fixes` first and the release notes after the disclosure, where the skill would end
  with the disclosure. The two commits are for review (tests first, then the fix); the squash makes them one.
- **Issue form** (`.github/ISSUE_TEMPLATE/bug.md`): version, Go version, OS, what you did, expected, seen instead;
  `issue.md` follows it, with the reproduction inline (no fork to link a branch on).
- **Tests**: grpc-go's `grpctest.Tester` style (`func (s) TestX`), in the package of the code: `encoding/proto`
  (`TestMarshalTooLarge`) and `grpc` (`TestEncodeTooLarge`, next to `TestEncode` in `rpc_util_test.go`), since the fix
  touches both.

## Duplicates checked (2026-10-31, unauthenticated GitHub search, repo:grpc/grpc-go)

Searches: `makeslice len out of range`, `codec Marshal panic large message`, `proto.Size allocate before size`,
`message too large panic`, `encode MaxUint32 allocation`. No duplicate. Related only by symptom:

- grpc/grpc-go#9056 (issue closed, not planned): "Segmentation fault, panic & memory spikes since v1.80.0", a
  `makeslice: len out of range` under load from a message mutated concurrently with marshaling; not this bug (no
  large message, a race in the application).
- #1010, #939 (prs closed, 2017): the codec's earlier buffer reuse; not this bug.

## Why the fix works

At the base, `codecV2.Marshal` computes `size := proto.Size(vv)` (no allocation; protobuf-go walks the message, so a
submessage held N times counts N times) and, for a size above the pooling threshold, calls
`mem.DefaultBufferPool().Get(size)`, which for a size beyond its largest tier does `make([]byte, size, allocSize)`
(`internal/mem/buffer_pool.go:356`). `make` panics when the size exceeds Go's `maxAlloc` (2^48 on linux/amd64). Only
after `Marshal` returns does `encode` reject a buffer over `math.MaxUint32` with `ResourceExhausted`
(`rpc_util.go:820-823`), and `SendMsg` the client's `MaxCallSendMsgSize` / the server's `MaxSendMsgSize`.

With the fix, `Marshal` returns `status.Errorf(codes.ResourceExhausted, "grpc: message too large (%d bytes)", size)`
(`encode`'s own text) when `size > math.MaxUint32`, before allocating, and `encode` returns an error from the codec
that is already a status error unchanged (other errors are still wrapped as `Internal`). Every send goes through
`encode` (`prepareMsg` on the client and in `serverStream.SendMsg`, `sendResponse` for unary replies), so both sides
get `ResourceExhausted`. The size check uses `uint64(size)` so that it compiles where `int` is 32 bits.

## If a reviewer asks

- **Cap the initial allocation and let `MarshalAppend` grow the buffer** (the finding's second option): does not fix
  it. protobuf-go's `MarshalOptions.marshal` allocates the whole size itself when the buffer is short
  (`google.golang.org/protobuf@v1.36.12/proto/encode.go:190`, `make([]byte, len(b), growcap(cap(b), len(b)+size))`),
  and panics the same way (`makeslice: cap out of range`, seen in the finding's server-side trace). The size must be
  refused before marshaling.
- **Return a plain error from the codec** (one file, no change to `encode`): `encode` would turn it into `Internal`,
  so a message between 4 GiB and 2^48 bytes, which gets `ResourceExhausted` from `encode` at the base, would get
  `Internal` instead. Keeping `ResourceExhausted` for every oversized message needs `encode` to keep the codec's code.
- **`encode` returning any status error unchanged** is a behavior change for custom codecs that return status errors
  from `Marshal`: their code now reaches the caller instead of `Internal` wrapping their text. No grpc-go codec or test
  relies on the wrapping (the package tests pass). A narrower alternative passes through only `ResourceExhausted`;
  the general one reads more simply and lets a codec choose its code.
- **Check in `encode` instead**: `encode` sees only `baseCodec` and cannot know the size before `Marshal`; computing
  `proto.Size` there too would double the cost for every message.
- **Check against `maxAlloc`, not 4 GiB**: `maxAlloc` is not exported and differs by platform; anything over 4 GiB is
  refused by `encode` anyway, so refusing it before allocating also saves allocating and marshaling 4+ GiB first.
- **Fix protobuf-go too**: `proto.Marshal` itself panics on such a message (above); that is a separate bug in
  google.golang.org/protobuf, not reported. grpc's codec needs the check either way to return `ResourceExhausted`.
- **New imports**: `encoding/proto` now imports `grpc/codes` and `grpc/status` (and through `status`,
  `genproto/googleapis/rpc/status`, already a module dependency of grpc-go). No new module dependency, so the
  `dependencies` check should pass; not run.
- **32-bit**: the tests skip where `int` is 32 bits (`proto.Size` cannot represent the size; that is protobuf-go's
  limit). `GOARCH=386 go vet` passes; the 386 tests were not run.

## The tests, and why they are legitimate

`TestMarshalTooLarge` (`encoding/proto/proto_test.go:147-163`) and `TestEncodeTooLarge` (`rpc_util_test.go:282-298`)
build the issue's message, a `structpb.ListValue` holding one 16 MiB `structpb.Value` 2^24 times (encoded:
281475144482816 bytes, just over 2^48; memory: 16 MiB plus 128 MiB of pointers; about 1 s), and assert
`codes.ResourceExhausted` from `codecV2.Marshal` and from `encode`. Sharing a submessage is ordinary protobuf-go use
(nothing forbids it, and `proto.Size` and `Marshal` handle it); the message is valid and well under memory. Nothing
is allocated near 2^48.

## Verification (go1.27.1 linux/amd64, `GOTOOLCHAIN=auto`; grpc-go's `go.mod` says go 1.26.0)

- At the tests commit 87decb761: `go test ./encoding/proto -run 'Test/MarshalTooLarge'` and
  `go test . -run 'Test/EncodeTooLarge'` both FAIL with `panic: runtime error: makeslice: len out of range` in
  `internal/mem.(*SimpleBufferPool).Get` from `encoding/proto.(*codecV2).Marshal` (`proto.go:74`).
- At the base, the other tests: `go test -timeout 7m ./encoding/... . -skip 'Test/(MarshalTooLarge|EncodeTooLarge)'`:
  ok (`encoding`, `encoding/proto`, `grpc`).
- At the fix b3a700339: `go test -timeout 7m ./encoding/... .` ok; `go test -race -cpu 1,4 -timeout 7m
  ./encoding/... .` ok (`grpc` 92 s); both new tests PASS; `gofmt -l` empty; `go vet ./encoding/proto .` and
  `GOARCH=386 go vet ./encoding/proto .` ok. `./scripts/vet.sh` was not run (it installs tools).
- The issue's program (a scratch `main` package in the worktree, removed): at the base, the panic pasted in the
  issue; at the fix, `rpc error: code = ResourceExhausted desc = grpc: message too large (281475144482816 bytes)`.
- End to end through a client (a scratch test in `test/` with `stubserver`, removed): `ss.CC.Invoke` with the same
  message as the request panics at the base (`makeslice: len out of range`, through `(*ClientConn).Invoke`); at the
  fix it returns `rpc error: code = ResourceExhausted desc = grpc: message too large (281475144482816 bytes)`. The
  server-reply path (`sendResponse` → `encode`) was not run; it is the same `encode` call.

## check.py

`PATH=/usr/local/go/bin:$PATH python3 -I .claude/skills/upstream-report/check.py grpc-codec-alloc-before-size-check
--worktree ~/etcd-fixes/grpc-codec-alloc-before-size-check --base bc90736a6fadc41582f9a23fb955bb66088f1bb8 --fork
NOFORK/grpc-go` (the script assumes an etcd-io target, `main` and a fork remote): two FAILs and three WARNs, each
decided as not applying to grpc-go:

- FAIL "no link to the test on the fork's branch": there is no fork; the issue's program reproduces inline, as
  grpc-go's form asks ("a recipe for reproducing the error"), and the PR carries the tests.
- FAIL "no 'Anything else we need to know?' section": etcd's form; grpc-go's has none. The disclosure ends the issue.
- WARN "names `Marshal`": `encoding.CodecV2.Marshal` is the public API the program calls.
- WARN "no permalink at the base": the script looks for etcd-io links; the PR has two grpc/grpc-go permalinks at the base.
- WARN "109 words": including the `RELEASE NOTES:` grpc-go requires (19 words); the prose is about 90.

## Hand-off

- Commit messages to rewrite (drafts): `encoding/proto: test marshaling a message too large to allocate` (no body);
  `encoding/proto: check the message size before allocating` ("A message whose encoding was too large to allocate
  made Marshal panic; it now fails with ResourceExhausted, as encode does for messages over 4 GiB."). Author and
  sign-off Frans Kaashoek <kaashoek@mit.edu>.
- To file: fork grpc/grpc-go, `git -C ~/grpc-go remote add origin <fork>`, then
  `git -C ~/etcd-fixes/grpc-codec-alloc-before-size-check push origin fix/grpc-codec-alloc-before-size-check`; file
  the issue (or the P4 report, above), then the PR with `#<issue>` filled in; sign the CLA when the bot asks.
