# etcd_safe restart: the interim axioms' drafts and the restated `NewServer_dist` (S0, 2026-11-26)

Not compiled. Companion of `plans/etcd-safe-restart-design.md` (coordinator notes) §3, §4.5. Branch
`etcd-safe-crash-s0/2026-11-26`. What S0 compiled is listed at the end; this file holds what cannot be compiled
yet (the Go change is not made) and what goes to the coordinator first.

## 1. Soundness finding: the C-I1 closed pair as designed (`dbCrashKeep_closeK`, `dbClosedCrash`) — dropped

The design's shape (a closed record `dbClosedKeep γ i0 Dn` made by `_closeK` **before** `DB.Close`, and a crash
law from it to `fileHoldsM i0 Dn`) is refutable, by two programs neither of which needs the open record:

1. *Commit after `_closeK`.* `_closeK` (like `_close`) gives back `dbHalf γ Dn`, half of bbolt's `boltState`, and
   `boltState ⊣⊢ ∃ ν, boltStateV` (`bbolt.boltState_eq_V`; `InvBbolt.lean`, `dbHalfV_dbHalf`). With `ownDB`'s
   other half the caller commits the live transaction (`Tx.Commit.spec`): the file holds `S ≠ Dn`, synced, and
   `dbClosedCrash` still gives `fileHoldsM i0 Dn`.
2. *Reopen after `DB.Close`.* `DB.Close.spec` gives `fileHoldsM i0 Dn` back (W3: `bfile_out`). The caller can
   `Open` it with `NoSync = true` (`Open.spec` allows any `o.ok`), commit `S` and then `Dn` again unsynced, `Close`,
   and hold `fileHoldsM i0 Dn` again while a crash may tear the unsynced pages.

**Decision (the lead, 2026-11-26): fix (a), no axiom.** bbolt-crash proves a crash-mode `DB.Close` as an atomic
update `<<dbCrashKeep γ i0 Dl Dn>> db.Close() <<fileHoldsMDur i0 Dn>>` (commit point at `bfile_out`; the fork gains
one line, an `fdatasync` in `Close` when the database is writable and `!NoSync`). A crash before the commit point is
`dbCrash`; after it, the proved `fileHoldsMDur_crash` (`backend/FileDur.lean:244`). So the draft file
`CrashInterimClose.lean` is deleted, and S0's closed backend keep `KeepBc` (`MemberBoot.lean`, `memberKeepRc`) is
left abstract with that instance named in its docstring: `fileHoldsMDur k.i0 k.Dn` with T10's payload of `k.Dn`.
D3's new interim axioms go from 4 + 2 to 2 + 2: `serve_dist`, `GracefulStop_dist`; `NewServer.specC_dist`,
`Serve_distR`.

## 2. `serve_dist` (pending the Go change: `server.serve` does not exist)

Go (design §1.3): `serve(s, addr) (*grpc.Server, error)` = `etcdstart.Serve`'s body returning the server. Lean text,
for `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/server/ServeK.lean` (namespace `etcd_dist`, the
variables of `ServeDist.lean`):

```lean
/-- `serve(s, a)` of a started member of the view `Γ` (DRAFT, pending the Go change): `Serve_dist.spec`'s
premises; on success the right to stop the gRPC server it returns (`grpcServing gs E`, `GracefulStopDist.lean`)
and the member's right to stop its etcd server, which `Serve_dist` consumes inside `memberUpL`. -/
abbrev serve_dist.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)]
    [π : NetProtoGS] (s : Loc) (a : GoString) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc) (γn : NetNames GF)
    (mid : w64) (Γ : DistView),
  (Γ.auth = true → ∀ a b : w64, Γ.au a = Γ.au b → a = b) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server ∗
      zapLoggerOk lg ∗
      ⌜v3rpc.ServerMethodSets ∧ apply.backendUnderQuota ∧ grpcRepliesFit ∧ srvLevels (GF := GF) ∧
        kvCongr ρ.rd.kv Γ.kv ∧ (Γ.auth = false ∨ ρ.rd.kv.hist = Γ.kv.hist)⌝ ∗
      (if Γ.auth then etcdstart.memberUpOnL s ρ E₀ lg γn mid (Γ.au mid) Γ.kv.lm (Γ.ls mid)
        else etcdstart.memberUpL s ρ E₀ lg γn mid Γ.kv.lm (Γ.ls mid)) ∗
      etcdAddrAt (Gg := hG.goose_globalGS) a Γ mid }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.serve)) (Val #s)) (Val #a))
  {{ (gs : Loc) (err : GoInterface), RET (PairV #gs #err);
      ⌜err ≠ GoInterface.nil⌝ ∨
      ⌜err = GoInterface.nil⌝ ∗ (if Γ.auth then True else ∃ (E : apply.AEnv GF) (dd : GoString),
        ⌜E.authOn = false ∧ E.cmp = E₀.cmp⌝ ∗ grpcServing gs E ∗ srvStopRight s E ρ.rd.raft.raft ρ mid dd) }}
```

- **Contract / why true:** `Serve_dist`'s (the in-process `etcdstart.Serve` proof per member, the address's
  protocol across machines), and: the gRPC server's run pool holds the serving stocks' store readers while idle
  (`grpcServing`'s reading); `serve` does not use `srvStopRight`'s channels' ownership (the handlers read
  `StopNotify`, a persistent view), so the right comes back. With `GracefulStop_dist` this lifts `HardStop.spec`'s
  "never served" scope for the dist line (its header, `EtcdServer__HardStop.lean:8-16`). `grpcServing gs E` is
  made only here, once per `gs` (`serve` makes a fresh one), from the serving stocks `memberUpL` holds
  (`srvServeStock`'s `srvRevokePoolN` store readers): the readers `GracefulStop_dist` gives back. `memberUpOnL`
  holds no `srvStopRight` and has auth on, so the auth arm gives no stop right (review F3,
  `notes/axiom-review/gracefulstop-dist.md`).
- **Design finding:** the design's `serve_dist` returns only "the right to stop it"; it must also return the etcd
  server's `srvStopRight` (and `srvStopReq`'s other parts, `srvBootApplied` and `srvDataDir`, persistent, from the
  member's facts), since `memberUpL` holds it and `Serve_dist` consumes `memberUpL` whole. The stop scope
  (`⌜E.authOn = false ∧ E.cmp = …⌝`) is `memberUp_stop`'s.
- **Retirement:** S2 (as `Serve_dist`); or restate `Serve_dist` itself if `etcdstart.Serve` returns the server.
- **Route:** translate (S2/S3 grpc over the net extension, not yet) → Go model (grpc model in-process, S1) → trusted
  code (none) → axiom (interim).
- **Restarts:** under R-A every incarnation calls `serve`, so `Serve_distR` (compiled over `etcdstart.Serve`) must be
  restated over `serve` with this post once the Go change lands (`serve_distR`); until then `Serve_distR` is the
  text a reviewer reads. Design finding: §3's table lists `Serve_distR` over `etcdstart.Serve`, which `MainLogger`
  will no longer call.

**The stopper** (`stopAt(s, gs, at)`, in `MainLogger`): no axiom. Its spec (P2/P4's, after the Go change):
from `grpcServing gs E`, `srvStopRight s E γ ρ id dd`, the boot evidence `srvBootApplied ρ` (its `AppliedIndex()`
wait) and `srvDataDir s dd`, it returns (`GracefulStop_dist`, then `EtcdServer.HardStop.spec` in the no-crash arm
N1, or `memberStop.law` in the crash proof).

## 3. The restated `NewServer_dist` (an approved axiom: for the coordinator first)

`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/NewServerDist.lean:271-331` (the post) and the header.

**Before (today):** the post is `specG`'s at the dist network names (`:271-331`), ending with
`srvStop.keep srv cfg E γrn γk`. Nothing in it survives a crash of the generation.

**After (proposed):** the post gains, before the error disjunction (as `NewServer.specC`'s
`NewServerCrash.lean:124-127`), the crash keeps of a first start, and the generation's keep pieces
`memberKeepR` needs (`dist/crash/MemberCrash.lean:822`):

```lean
  {{ (srv : Loc) (err : GoInterface), RET (PairV #srv #err);
      -- (etcd_safe, proposed) raft's crash token of the vacancy `NewServer` arms, for the generation's next crash
      (∃ x, nodeCrashTok γ.cl id x) ∗
      -- (etcd_safe, proposed) the snapshot directory's crash token (D-T7-2's, `specC`'s)
      srvSnapKeep γ id cfg.DataDir' ∗
      -- (etcd_safe, proposed; B5 of notes/etcd-dist-d6.md) the WAL's and raft's durability keeps a first start
      -- allocates: T2's crash-aware invariant with its token and the stop's token, the WAL area's invariant with
      -- its crash token, and the durable spine `member/snap` (T8, D-T7-4)
      (∃ (νk : WalNamesK GF) (h : WalH GF) (cid : w64) (jd J : Fs.Ino),
        ⌜h.dir = srvWalDirOf cfg.DataDir' ∧ h.md = walMetaEnc id cid ∧ (cfg.DataDir', jd) ∈ h.R ∧
          (h.r, h.jr) ∈ h.R ∧ h.r ≠ cfg.DataDir' ∧ IsUnder h.r h.dir⌝ ∗
        memberCrash.memberDurKeep γ id νk h ∗ memberCrash.memberWalKeep h ∗
        memberCrash.osSpineDur jd [go!"member", go!"snap"] J) ∗
      ((⌜srv = null ∧ err ≠ GoInterface.nil⌝ ∗ threadTok) ∨
      ⌜err = GoInterface.nil⌝ ∗ threadTok ∗ ∃ (γn : NetNames GF) … (unchanged) … ∗ srvStop.keep srv cfg E γrn γk) }}
```

Why (the axiom's docstring gains): the keeps are ghost state and invariants the construction allocates
(`newRaftNode`'s `rnDurInvK`, `wal.Create`'s `walInv`, `TouchDirAll`'s durable names); the construction does not
depend on them; their soundness is T2's/T5's crash laws' (proved), not a new claim about Go. `dist-axiom-diff`
then lists them as `dev` lines whose reason is "crash keeps; `specG` has no crash keep: retiring `NewServer_dist`
needs `specG` restated with them (`specGK`, open)".

**Not covered by any post-only restatement (design findings, for the coordinator):**
* **B4, a crash inside the call.** `NewServer_dist` and `NewServerC_dist` are triples: their exclusive
  preconditions (`raftState`, `nodeVacant`, the slice, `Hlslot`, `Hγa`; a restart's image) are the callee's until
  it returns. A crash during the first `NewServer`, before `wal.Create`'s rename is durable, leaves a first start
  again (`memberFirstCrash.law`), whose `memberFirst` needs those resources back. So the restated axioms need a
  crash-aware form (a keep slot in the precondition, `memberKeepInv`, that the call keeps valid at every step:
  kvnet's `kvGen_boot` allocates its file invariant before `StartNode` for this reason), or the generation's boot
  must keep them in an invariant the axiom's precondition names. This is the same question for the in-process
  `specG`/`specC` (approved specs), so it is a coordinator decision.
* **The backend's record.** `dbCrashKeep` cannot be a post item: the running backend needs it at every commit
  (T10: it lives in the crash-aware `KeepB`), so it must go *into* `NewServer` (the slot), not out.
* **The first start's lessor and auth slots** (`memberNamesShare`): `memberFirst` has no row for them, and after a
  crash inside the first `NewServer` they are gone (`Hlslot` is consumed by the call). At lease mode `.none` and
  auth off they are needed only because `NewServer_dist` takes `Hlslot` unconditionally.

## 4. Route rows (translate → Go model → trusted code → axiom)

| Axiom | Translate | Go model | Trusted code | Axiom (why now) | Where |
|---|---|---|---|---|---|
| `serve_dist` | `server.serve` not written; grpc over net: phase 7 S2/S3 | grpc model in-process (S1) | no | interim, pending the Go change | §2 above (not compiled) |
| `GracefulStop_dist` | grpc-go is a trusted model; `GracefulStop` body not translated | `models/grpc` has it (`server.go:1405`), no proof | no | interim | `Spec/.../etcd/dist/GracefulStopDist.lean`, `Proof/.../etcd/dist/GracefulStopDist.lean` |
| ~~`dbCrashKeep_closeK`~~, ~~`dbClosedCrash`~~ | bbolt translated, `DB.Close` proved in-process | n/a | no | **dropped** (§1): bbolt-crash proves the crash-mode `DB.Close` (no axiom) | — |
| `NewServerC_dist` (`NewServer.specC_dist`) | rafthttp across machines: S5 | none | no | interim, as `NewServer_dist`; also needs `NewServer.wp_proofC` (`sorry` at `NewServerCrash.lean:81`) | `Spec/.../etcd/dist/NewServerCDist.lean`, `Proof/.../etcd/dist/NewServerCDist.lean` |
| `Serve_distR` | as `Serve_dist` | grpc model in-process | no | interim; or `Serve_dist` restated with the lessor free at `.none` | `Spec/.../etcd/dist/ServeDistR.lean`, `Proof/.../etcd/dist/ServeDistR.lean` |
| `NewServer_dist` restated | as today | none | no | changed approved axiom | §3 above (not applied) |
