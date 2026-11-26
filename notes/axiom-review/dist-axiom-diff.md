# The distributed interim axioms against their in-process sources (M1, 2026-11-26)

A mechanical comparison, not an `axiom`-skill review. It was done while writing M1's axiom-tok entries (branch
`etcd-safe-m1-top/2026-11-25`). It compares each `*_dist` interim axiom's statement with the proved in-process
spec it copies, as token lists: comments, Iris names and layout removed. It is now the gate `etc/dist-axiom-diff.py`
(`etc/gates.sh`, beside `mode`), with every listed difference and its reason in `etc/dist-axiom-diff-allow.txt`.

## The finding: `NewServer.specG_dist` without `specG`'s `etcdURLsFit`

**Before** (HEAD `ad0a4756a0`): besides the header's three listed changes, the copy lacked one premise of its
source:

```
NewServer.specG  vs  NewServer.specG_dist:
  - → etcdURLsFit U.peer → etcdURLsFit U.client
  + (nothing)
```

- **What the premise says.** `specG`'s `etcdURLsFit U.peer → etcdURLsFit U.client` bounds the member's peer and
  client URLs: at most 64, of at most 1024 bytes each, each `http://host`.
- **Why `specG` has it.** fmt stage 1 added it (`c486fbb43f`, 2026-11-24, #9 decision 7126397740 (2)) for the
  `strings.Join`s of those URLs: `publishV3`'s log lines and the transport's `X-PeerURLs`.
- **Why the copy lacked it.** `NewServer_dist` was copied (`db309fe291`) from a base without that commit. The
  premise then reached `specG` through a merge, and the copy never got it.
- **What that meant.** The trusted axiom claimed `NewServer` never panics for URL configurations the proof needs
  to exclude. Its header still said "nothing else, the rest is its text verbatim".
- **M1 was not affected.** Each member has one URL of each kind, and a valid address is at most 21 bytes
  (`AddrPlain.lean`, `addrOk_addrFits`).
- **What was not checked.** Whether Go, or the model, panics past the bound.

**Fix** (the M1 lead's decision, 2026-11-26: one more premise weakens the axiom, and no axiom is added):

- The premise is restored in `specG_dist`, in `specG`'s position.
- The header lists every difference, and the gate checks the list.
- `MainLogger.wp_proof` discharges the premise from `WellFormed`'s `addrOk` of the member's peer and client
  addresses (`addrOk_addrFits`, `etcdURLsFit_httpURL`).

**After**: `NewServer.specG` against `NewServer.specG_dist`, every difference (the `dev` lines):

```
+ [ π : Net.NetProtoGS ]                                      binder: the net extension's protocol ghost state
- GF ) ( γn : NetNames                                        γn no binder (the post gives it)
- netHttpOk γn                                                #Hnet replaced by #Hpeers ...
+ ( □ ∀ ( pid : w64 ) ( a : GoString ) , ⌜ pid ∈ γ.vs ∧ pid ≠
+ ∧ go!"http://" ++ a ∈ dir pid ⌝ -
- ⌜ γn.N = srvNet          + etcd_dist.httpAddrAt ( Gg := hG.goose_globalGS )
- ∧ γn.dir = dir ⌝         + pid a ) ∗ etcd_dist.noProxyEnv   %Hγn moved to the post; #Hnoproxy added
+ γn : NetNames GF ) (                                        the post's ∃ γn
+ γn.N = srvNet γ ∧ γn.dir = dir ∧                            the post's facts of γn (%Hγn's before)
```

## The other axioms

| axiom | source | differences | result |
|---|---|---|---|
| `KV_Put_dist` | `kv.Put.spec` | 17 | as N2's review (`n2-kv-dist.md`) states: `isKv kv γ false` replaced by `kvClientAt` at `Γ`, `γ := Γ.kv`, `□?false` dropped, `Γ.auth = false` added, `kvErr` dropped from the error arm; nothing else |
| `KV_Get_dist` | `kv.Get.spec` | 13 | the same, without the auth premise (a read) |
| `KV_Delete_dist` | `kv.Delete.spec` | 16 | as `KV_Put_dist` |
| `KV_Compact_dist` | `kv.Compact.spec` | 13 | as `KV_Get_dist`, `γ.cmp`/`γ.cret` the view's |
| `Txn_Commit_dist` | `txn.Commit.spec` | 20 | as `KV_Put_dist`, the builder's endpoints `eps` |
| `bootstrap.wp_proof_dist` | `bootstrap.spec` | 3 | the binder `π`, `etcd_safe`'s shape premises, the precondition `bootRTOk`; also machine-checked: `bootstrap.specDist_of_spec` derives it from `bootstrap.spec` |
| `Serve_dist`, `NewPeerHandler_dist`, `PeerServe_dist` | none | | no in-process spec they copy (`nosource` lines: `Serve_dist`'s analogue `etcdstart.Serve.spec` is a different statement; `etcdhttp` is untranslated; `http.Serve_ok` at the raft handler is another statement) |

None of the listed differences strengthens an axiom beyond its reviews:

- Every premise or precondition added (`Γ.auth = false`, the shape premises, `bootRTOk`, `Hpeers`, `noProxyEnv`)
  restricts the axiom.
- Every post change weakens it: `kvErr` is dropped, and `γn` moves into the post's `∃`.
- The replaced preconditions are the reviewed ones: `isKv` by `kvClientAt` (N2 §C), and `netHttpOk` by `Hpeers`
  (plan §17.3).
