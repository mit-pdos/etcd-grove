# The per-type Scope's two blockers: `grpc.serve`'s pool and `pbEnc` across heaps

**Reviewed** 2026-11-07 at `lean` `ad87892323`. The two blockers were raised by etcd-grove-82's
workflow review of the per-type Scope and compiled by etcd-grove-c9.

The bug record, with the reach of each, is `notes/per-type-blockers.md`.

## (a) `grpc.serve`/`grpc.serveStream`: the free pool `S`, `n`

**Verdict: refuted at genuine kinds.** The derivation is on branch `axiom/grpc-serve-pool`
(`1ad2cc63a0`), in `Proof/github_com/mit_pdos/etcd_grove/examples/axiomcx/grpcservepool/False.lean`:

- `anyHandler_ok (mh srv ics Spec) : ⊢ grpcMethodOkMd mh srv ics ⌜False⌝ Spec`, at
  `pbCompactionRequest`/`pbCompactionResponse`. It uses no axiom.
- `served_call_fails`: the pre is `isPkgInit grpc ∗ grpcServerAt addr [] [(name, nilHandler, srvv)] ∗
  grpcConn conn [addr] [] [] ∗ ctxOk ctx cd ∗ opts ↦*□ [] ∗ inp ↦ req ∗ out ↦ rep`, with
  `req.unknownFields' = nil`. The post is `|={⊤}=> WP conn.Invoke(ctx, name, inp, out, opts) {{ v,
  ⌜∃ err, v = #err ∧ err ≠ nil⌝ }}`, by `grpc.serve … ⌜False⌝ 0`.
  - `#print axioms`: `grpc.serve`, `ClientConn.Invoke.wp_proof`, and the opaque `grpcServerAt`,
    `grpcConn`, `grpcServes`, `grpcPeerOpt` and `grpcWrotePeer` (with their `_persistent` laws), plus
    the opaque Go types. No `sorry`.
- `anyStreamHandler_ok`: the same for `grpcStreamMethodOkR` at `pbWatchRequest`/`pbWatchResponse`,
  with no axiom. The client-side failure through `NewStream`/`RecvMsg` is not compiled; it carries
  over.

## (b) `pbEnc_ok`: two heaps, one address

**Verdict: refuted at the genuine `pbEntry`.** The derivation is on branch `axiom/pbenc-heaps`
(`0d40894e13`), in `Proof/github_com/mit_pdos/etcd_grove/examples/axiomcx/pbencheaps/False.lean`:

- `world_decode`: in a world built by `fupd_soundness` with Perennial's `goose_init` from an empty
  heap, holding the persistent cells of `l`'s `Entry` fields and `pbMsg` (from `inv_alloc_open`),
  `entDecode (pbEnc raftpb.Entry.ty l) = some (entWith d)`.
- `pbEnc_heaps_false`: `d = []` and `d = [1]` give `False`.
- `#print axioms`: `propext`, `Classical.choice`, `Quot.sound` and `pbEnc_ok`.
- The hypotheses are the ambient semantics instances, and the layout of `l`'s fields: distinct
  addresses in range, as in Go.

## The fixes (per-type stage)

- (a): the pool tied to `threadTok` and adequacy's thread bound.
- (b): `pbEnc` keyed on content, with `pbEnc_ok` derived from one `_sat` per registered type.
