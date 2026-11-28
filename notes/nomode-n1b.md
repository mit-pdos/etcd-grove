# No auth modes, stage N1b (2026-11-28)

The plan: `~/coordinator-notes/plans/nomode-packet.md` (local), "Staging plan v2". Stage N1 (the model
changes, the porting lemma) is `notes/nomode-n1.md`.

## N1b-2: one KV model, the fold from `srvAuthSt0`

Decided by the user: no auth modes; one `kvModel`, one `kvRevLb`. The start auth state is fixed at
`srvAuthSt0` (no new `KVNames` field: every start today is a fresh boot).

### Trusted-visible definitions: before / after

`kvRevLbZ`/`kvRevLb` (`InvRequest.lean`) are named by the specs `kv.Put`, `kv.Compact`, `txn.Commit`
(`Spec/go_etcd_io/etcd/client/v3/`), `EtcdServer.Compact` and the client `_dist` contracts. Their text
is unchanged:

```lean
def kvRevLbZ (γk : KVNames) (n : Int) : IProp GF :=
  iprop(∃ L₀ : List EntryModel, monoListLbOwn γk.rlog L₀ ∗ ⌜n < (kvModel γk L₀).length⌝)
```

What changes is `kvModel` (and `kvLeases`), which they are written in:

**Before:**

```lean
def kvModel (γk : KVNames) (L : List EntryModel) : mvcc.Log := kvRaftOf γk.c0 γk.ch0 γk.log0 L
def kvLeases (γk : KVNames) (L : List EntryModel) : LeaseTable := kvTableOf γk.c0 γk.ch0 [] L
```

**After:**

```lean
def kvFold (γk : KVNames) (L : List EntryModel) : OnState :=
  kvRaftOfOn γk.c0 γk.ch0 (srvAuthSt0, γk.log0, []) L
def kvModel (γk : KVNames) (L : List EntryModel) : mvcc.Log := (kvFold γk L).2.1
def kvAuth (γk : KVNames) (L : List EntryModel) : auth.AuthState := (kvFold γk L).1
def kvLeases (γk : KVNames) (L : List EntryModel) : LeaseTable := (kvFold γk L).2.2
```

`srvAuthSt0 := auth.bump auth.bootState` (disabled, revision 1, no user or role) moved, unchanged, from
`KVModelM.lean` to `KVAuthModelDefs.lean`, which `InvRequest.lean` now imports (defs → defs).

**Why the meaning is unchanged where it was used.** `kvFold_off` (from the porting lemma
`kvRaftOfOn_disabled`, `notes/nomode-n1.md` step 4): along a log with no `AuthEnable` above `c0`
(`noAuthEnable γk.c0 L`) the fold's auth state stays disabled, and its log and table are
`kvRaftOf γk.c0 γk.ch0 γk.log0 L` and `kvTableOf γk.c0 γk.ch0 [] L`. Every log the auth-off invariant
`kvInv` holds is `plainLogM`, whose entries are of a proposer's kind (`putgetKind`), a compaction, a
grant or a revocation, never `AuthEnable` (`noAuthEnable_of_plainLogM`). `kvRevLbZ`'s `L₀` is a prefix
of the requested log, which is that log. So under auth off `kvRevLbZ γk n` holds of the same `n` as
before. Under auth on, the fold is `kvModelOn γk srvAuthSt0` (`kvModelOn_srv`, `rfl`): the auth-aware
model the `*On` invariants already use, so `kvRevLb` now names the model those clients follow (the merge
of the twins, N2/N5, can use it).

### What else moved

- `appliedTable` (the lessor's table, the off twin of `appliedTableM true`) and `bkRestAtL` (the off
  leased rest image) keep their value: they are now written `kvTableOf γr.kv.c0 γr.kv.ch0 [] (γr.raft.pre
  ++ A)` (`kvTableOf γk.c0 γk.ch0 [] L`), which is what `kvLeases` was. They merge into the fold with
  their twins in N2. Neither is named by a trusted statement.
- New lemmas: `kvFold_off`, `kvModel_off(M)`, `kvLeases_off(M)`, `kvLeases_ne0_of`, `kvModel_extends`,
  `kvModel_prefix`, `kvModel_length_le`, `kvFold_snoc`, `kvFold_congr` (`InvRequest`);
  `kvEntryOn_snd_nonwrite`, `kvEntryOn_snd_disabled`, `noAuthEnable_of_plainLogM`, `noAuthEnable_sub`,
  `srvAuthSt0_enabled` (`KVAuthModelDefs`, with `kvRaftOfOn_length_le` moved there from `KVApplyOn`);
  `kvFold_boot`, `kvModel_bootE` (`InvBuild`); `kvModelOn_srv`, `kvLeasesOn_srv`, `kvStOn_srv`
  (`KVAuthModel`). The requested-entries lemmas `kvOpOn`, `kvEntryOn_above/_filler/_emptyV2`,
  `kvRaftOfOn_ops` moved from `KVAuthModel` to `KVLemmas` (for `kvModel_eqv`).
- The R declarations: `kvModel_ne_nil`, `kvModel_snoc_nonwrite`, `kvModel_eqv`, `kv_cert_floor`,
  `kvModel_boot` are re-proved over the fold with no new premise; `kvModel_snoc_state` takes
  `noAuthEnable γk.c0 L` (its two callers pass it from `plainLogM`); `kv_applied_step`, `snapRecv_image`,
  `snapRecv_imageR`, `NewServer.wp_proofRG` rewrite with `kvModel_offM` from the `kv_log_plain` they
  already had.
- No top-level statement, axiom or premise changes.
