# M2 apply side, Draft: review round 6 (2026-10-30)

Reviewed: `m2-apply` at `26e8634379` ("round 5 and its repair": F5-1, item 19 gains `kvCertInv(M)`
and item 6 the commit-step plan; F5-2, `Compact.specD` at `isServerRead s E ρ.rd`; items 8/12/13
committed to S3-3). Targets: the three Drafts and the consolidated item list of
`notes/m2-apply-plan.md`, "The switch in place". Judged under the in-place convention (the user's
Q6 (a)). "The off texts mean today's by laws, not `rfl`" is not re-raised.

- **Checked:** `etc/lean-check.py -q -a` on the three Drafts: 0 errors.
- **Go:** I read no Go code beyond the earlier rounds'. I found no Go bug; nothing goes to `issues/`.

## Round 5's repairs

### F5-1 (the commit step): the plan is sound, and an existing lemma does the work

I checked the plan against `EtcdServer__processInternalRaftRequestOnce.lean`, `kv_prop_au` and
the masks in `SrvRaftLog.lean`.

**Where things run.**
- `kv_prop_au_M` is called with mask `⊤` (`EtcdServer__processInternalRaftRequestOnce.lean:225-228`).
  It calls `kv_prop_au` at that mask (`ReqOn.lean:681`).
- `kv_prop_au` is a fupd `={E}=∗ srvPropAu1 …` (`KVLemmas.lean:235-240`). It is the *update* it
  returns that runs at `⊤ \ ↑srvRaftN` (`SrvRaftLog.lean:569`).
- So "compare before the atomic update is built" means: in `kv_prop_au`'s leading fupd, at `⊤`.
  That is possible. Item 6's first clause ("`kv_prop_au` runs at `⊤ \ srvRaftN`") is misworded:
  the update runs there, not the lemma (S6-3).

**What is at hand at that point.**
- `srvRaftLogInv ρ.raft`: from `raftPropose` (`#HrLog`, `:214`, before the call).
- `kvCertInv ρ.raft ρ.kv`: from item 19's new conjunct, next to `#Hclog` in the destructured
  `srvReqFieldsAtM` (`:520-522`).
- The mask: `kv_prop_au`'s `hE` has to grow from `↑kvN ⊆ E` to `kvN`, `kvcN` and `srvRaftN`. The
  only caller passes `⊤`, so this costs nothing.

**The comparison, step by step.**
1. `cmpReach γk r` gives `kvCert γk l` with `r < l.length`.
2. `kv_cert_read` (`KVLemmas.lean:766`, needs `kvcN`) turns the certificate into one of two cases:
   - `l.length ≤ 2`; or
   - `srvRLogLb γ A` with `kvModel γk A = l`.
3. In the first case: `kvCertInv`'s `2 ≤ γk.log0.length` (`InvRequest.lean:404`) and
   `kvRaftOf_extends` give the bound at every log. No lower bound is needed.
4. In the second case: **`srvReqLogLb_of_rlogLb`** (`SrvRaftLog.lean:1025`, mask `⊇ srvRaftN`)
   turns `srvRLogLb γ A` directly into `srvReqLogLb γ L₀ = monoListLbOwn γ.raft.log L₀` with
   `srvEqv γ A L₀`. It needs no opening of `kvInv`. `AuthTieRead.lean:134` already uses it this way.
   - The plan's route (`srvRLog_lb` after opening `kvInv`, then `monoListLbOwn_get`) also works, but
     takes two steps for what this lemma does in one. Name this lemma in item 6 (S6-3).

**Inside the update, at the commit.**
- `srvReqLogLb_prefix` (`SrvRaftLog.lean:1016`) needs no mask: it gives `L₀ <+: L` from the
  invariant's `srvRLog γ L`.
- `kvModel_eqv` (`KVLemmas.lean:162`; its `c0 ≤ ai0` is the invariant's `Hok.2.2.1`) and
  `kvRaftOf_prefix` (`KVModelDefs.lean:504`) give `r < (kvModel γk L).length`.
- That is `cmpEntryOk γk γk.cmp L e`, with `γk.cmp = true` and `compactPropOkD` from the form.
- The state is unchanged (`kvModelSt_snoc_nonwrite`, as in the no-write branch, `KVLemmas.lean:285`).
- For the write forms, `cmpLogOk` extends vacuously, since `plainReq_nonCmp` excludes a
  compaction.

**Verdict on F5-1:** sound.

### Does `kvCertInv` in `srvReqFieldsAt(M)` have a producer?

**In the off mode: yes.**
- `start` builds `isServerReq` from `srvReqBuilt` (`EtcdServer__start.lean:452-480`).
- It holds `#Hkvi : srvKVInvs E γr`, which contains `kvCertInv γr.raft γr.kv`
  (`InvApplier.lean:333`), and `Hρrd : ρ.rd = γr` (`InvBuild.lean:339`).
- `{ρ with wait := γw}.kv` is `ρ.rd.kv`, so the conjunct is one `iframe` away.

**In the on mode: yes.**
- `start.specOn`'s proof builds `isServerReqM true` (`EtcdServer__start.lean:975-1009`).
- `srvKVInvsM true` is `srvKVInvsOn ∗ srvUberOn` (`ServerOn.lean:384-387`), and `srvKVInvsOn` holds
  `kvCertInvOn γr.raft γr.kv srvAuthSt0` (`KVApplyOn.lean:300`).
- That is `kvCertInvM true …` (`ServerOn.lean:241-245`).
- `kvCertInvM false` reduces to `kvCertInv` by `match`, so `srvReqFieldsAtM_false` stays `rfl`.

**Other producers:** none. `start`'s two branches are the only places that build
`srvReqFieldsAt(M)` (every other `iunfold srvReqFieldsAt(M)` is a consumer).

**But the same check fails for item 19's other conjunct, the tie, in the on arm. See R6-1.**

### F5-2 (`Compact.specD` at `ρ.rd`): resolved

- **The proposal's certificate now lands at the right names.**
  - `isServerRead s E ρ.rd`'s `srvKVInvs E ρ.rd` gives `E.γ.cok = ρ.kv.cok`.
  - G2 (a)'s `certOk` at `E.γ` therefore becomes a `kvCert ρ.kv`, which is the form's `cmpReach ρ.kv r`.
- **The mode.**
  - `ρ.kv.cmp = true` comes from item 19's tie in `isServerReq` and `⌜E.cmp = true⌝`.
  - `E.authOn = false` is in `isServerReq`, so `processInternalRaftRequestOnce.spec` is used at
    `on = false`.
- **The producers can supply it:**
  - `start`'s post gives `isServerReq s E {ρ with wait := γw}` and `isServerRead s E γr`, and
    `srvStarted` gives `⌜ρ.rd = γr⌝`;
  - the record update keeps `.rd`.
- **The only caller of the spec is `compactableOk_server`** (`CompactEnv.lean:71-104`); item 15
  restates it the same way. `kvServer.Compact` has no proof here that calls it.
- **Uncertain, and outside these targets** (the storage side's S4): `compactableOk_server` needs the
  `start`-made views (`isServerReq(C)`, `isServerRead`), but its only user is
  `NewServer.wp_proofCompact` (`NewServer.lean:2033`, a `sorry`). There the compactor's
  `compactorRun c` (`InvRun.lean:291`) is built before `start` exists. When that `sorry` is
  proved, the compactor's contract has to take the views later, for example as `T`/`P`. F5-2 does
  not make this worse.

### Items 8/12/13 (S3-3): the commitment is sound

- `applyEntryNormal`'s proof holds everything the derivation needs at `⊤`
  (`EtcdServer__applyEntryNormal.lean:248-276`):
  - `#HAm : srvRLogLb γr.raft (A ++ [m])`;
  - `#Hkvi`, from which `kvInv` (`#HkI`) and `srvRaftLogInv` (`#HrI`) are taken;
  - `kv_log_plain` already opened at `⊤` (`:272`).
- The lemma is round 5's `kv_cmp_entry`, through `srv_eqv_prefix` at
  `(opsOf (A ++ [m])).length`:
  - a compaction entry has data, so it is no filler and `opsOf (A ++ [m]) = opsOf A ++ [m.toLE]`;
  - the invariant's entry at index `(opsOf A).length` has `m`'s type and data, so it decodes to
    the same request;
  - `kvModel_eqv` makes the two prefixes' models equal;
  - `cmpEntryOk` reads only the type and data, so the claim moves over.
- In the on arm, `kvInvOn`'s `plainLogOn` excludes a compaction, so `cmpAdmit` is vacuous there
  (`kv_log_plain_on`).
- It still needs S-5's `E.cmp → kbCmpM E.γ.kb` law (carried, S6-5).

## First tier

### R6-1. Item 19's tie in `srvReqFieldsAtM`'s on arm has no producer: `start.specOn`'s post becomes unprovable

- **Principle:** Sound/Complete. An approved text's postcondition must be provable from its
  precondition.
- **What item 19 says.** The tie `⌜ρ.kv.cmp = E.cmp⌝` goes into `srvReqFieldsAtM` "at the same
  place in both texts". This is round 4's S4-1 repair: "in both arms is simplest; with `kvInvOn`
  the on arm is vacuous".
  - The on arm is vacuous for its *consumers*: auth on means no compaction.
  - It is not vacuous for its *producer*, which must prove it.
- **Evidence.**
  - `EtcdServer.start.specOn` (`Spec/…/EtcdServer__start.lean:60-73`) gives
    `isServerReqM true s E {ρ with wait := γw}`. With item 19, that holds the tie.
  - Its proof builds it (`EtcdServer__start.lean:979-1009`) from `isServerBuiltOn`
    (`StartOn.lean:67-100`). Neither source has the tie:
    - `srvReqBuiltM true` holds `kvInvM true` (= `kvInvOn`), with no tie;
    - `srvKVInvsM true` (`ServerOn.lean:387`) is `srvKVInvsOn ∗ srvUberOn`, and `srvKVInvsOn`
      (`KVApplyOn.lean:299-301`) has no tie. Item 19 adds the tie to `srvKVInvs` only.
  - Nothing else in `isServerBuiltOn` mentions `E.cmp` or `ρ.rd.kv.cmp`.
  - Item 14' gives `NewServer.specM` the premise `ρ.rd.kv.cmp = false` "since their posts'
    `srvKVInvs` carries item 19's tie". But `specM`'s on arm posts `srvBuiltG true`, which carries
    `srvKVInvsM true`, not `srvKVInvs`. The premise is never stored where `start.specOn` could read
    it.
- **Callers affected:**
  - `start.specOn`'s proof;
  - through it, the auth-on servers' request path (the examples' `Serve`, `authkv`), which reads
    `isServerReqM true`.
- **Cause.** Like rounds 1-5, this comes from a previous round's repair (round 4's S4-1). It
  surfaces now because round 5 made me check `srvReqFieldsAtM`'s producers.
- **Restatement** (either is cheap; (b) touches no auth-on text):
  - **(a)** Item 19 also adds `⌜γr.kv.cmp = E.cmp⌝` to `srvKVInvsOn` (or to `srvKVInvsM true`'s
    arm).
    - `NewServer.specM`'s proof makes it from 14''s premise and `envAgree`
      (`E.cmp = E₀.cmp = false`).
    - `start.specOn` frames it through `Hρrd`.
    - Cost: the positional destructurings of `srvKVInvsOn` move (`EtcdServer__start.lean:1042`;
      `ReadOn.lean:275, 587, 602, 816`), and the `srvKVInvsOn` producers in the on family.
  - **(b)** State the tie in `srvReqFieldsAtM` by the mode:
    - define `kvTieM on γk E := match on with | false => ⌜γk.cmp = E.cmp⌝ | true => True`, and put
      `kvTieM on ρ.kv E` at the same place;
    - `srvReqFieldsAtM false` still reduces to `srvReqFieldsAt` by `rfl` (as `kvCertInvM false`
      does);
    - `start.specOn` proves `True`;
    - mark it as the scope "auth on means compaction off" (round 3's S3-1).
  - Either way, item 14''s sentence should name where `specM`'s premise lands in each arm.

Nothing else is in the first tier.

## Second tier

### S6-1. The server Draft is behind item 19 (F5-1 (i) was made only in the plan)

- **`srvReqFieldsAtD`** (`M2ApplyDraft.lean`, "The request path's mode") is item 19's drafted text
  ("(`srvReqFieldsAtD`, `srvKVInvsD`)"). It still has no `kvCertInv ρ.raft ρ.kv`.
- **Its docstring** still says "this conjunct is `kvInv ρ.raft ρ.kv ∗ ⌜ρ.kv.cmp = E.cmp⌝`".
- **`cmpReach`'s docstring** still says only that the form is carried "to the commit, where the
  KV invariant records the revision". It does not say that the bound is taken before the update
  (round 5's ranking, item 3, not done).
- **Restatement.**
  - Add `kvCertInv ρ.raft ρ.kv` to `srvReqFieldsAtD`, next to `kvInvD`. Its off law is unchanged
    in proof (`iframe`).
  - Restate the docstring.
  - Add one sentence to `cmpReach`'s docstring: the commit's lower bound
    (`srvReqLogLb_of_rlogLb` at proposal time, `srvReqLogLb_prefix` inside the update).
  - The user approves the list *and* the Draft's text; they should agree.

### S6-2. The plan's Gaps entry G4 contradicts item 6

- G4 (plan, "Gaps") still says "`kvCertInv` opened beside `kvInv`". Round 5 showed that this
  cannot close the comparison inside the update.
- It also still says "the invariant's `NoDelPutAt`", which F-5 removed.
- The Probe will read G4.
- **Restatement:** G4 := item 6's commit-step text, with the lemma names of S6-3.
- In the same vein, also update:
  - "Still open" still lists S3-3, which items 8/12/13 now adopt;
  - "What `applyAll`/`run` need" still describes item 12/13's conjuncts (superseded; mark it).

### S6-3. Item 6's commit-step wording

- Change "`kv_prop_au` runs at `⊤ \ srvRaftN`" to: "`kv_prop_au`'s update runs at
  `⊤ \ srvRaftN`; the lemma itself at the caller's `⊤`".
- Name the route:
  - `kv_cert_read`, then **`srvReqLogLb_of_rlogLb`** (one step, no `kvInv` opening), in the
    leading fupd;
  - `srvReqLogLb_prefix` with `kvModel_eqv` and `kvRaftOf_prefix` inside the update.
- State the internal signature changes:
  - `kv_prop_au` and `kv_prop_au_M` gain `kvCertInv(M)` and `srvRaftLogInv`;
  - their mask premise grows to `kvN`, `kvcN` and `srvRaftN`;
  - the caller's `⊤` and `#HrLog` cover both.

### S6-4. Item 19's positional consumers of `srvReqFieldsAt(M)`, two outside the package

Adding two conjuncts beside `kvInv` leaves the earlier indices in place. A pattern that ends at
the `Cfg` conjunct still breaks:
- `EtcdServer__processInternalRaftRequestOnce.lean:522` ends `#Hclog, %Hcfgnn`. The `%` would now
  receive the spatial rest.

Patterns that end in `-` absorb the new conjuncts:
- `client/v3/ServeFromStart.lean:86, 160` and `api/v3rpc/ServerKV.lean:875`. These are
  **other packages unfolding `srvReqFieldsAt`**, an existing missing-law case (PRINCIPLES,
  "A client does not unfold").
- `EtcdServer__Txn.lean:670`, `MemberList.lean:45`, `AuthGuard.lean:233` and `ReadOn.lean:120`.

**Restatement:** list them under item 19. When `srvKVInvs` gets its projection laws, give
`srvReqFieldsAt` the ones its outside unfolds use (the peers, auth, fields), so that these
packages stop depending on its order.

### S6-5. Still open (carried)

- S-5: the `kbCmpM E.γ.kb ↔ E.cmp` law, needed by S3-3's in-proof derivation (`cmpAdmit_of_entry`'s
  `hkb`).
- S-2'/G2 (Q3): F5-2's `ρ.rd` serves both (a) and (b).

## What is good

- **F5-1's design is right, and cheaper than written.** The comparison at proposal time and a
  mono-list lower bound inside the update are exactly what the masks allow. The lemma that turns a
  committed prefix into a lower bound of the server's log already exists and is already used this
  way (`AuthTieRead.lean:134`).
- **The `kvCertInv(M)` conjunct has a producer in both modes** (`start`'s two branches). It keeps
  both `rfl` laws, since `kvCertInvM false` reduces by `match`.
- **F5-2 is the minimal fix.** One premise changes, and every producer of the views (`start`)
  supplies `ρ.rd = γr`.
- **The S3-3 commitment is sound.** `applyEntryNormal`'s proof has the resources at `⊤`. Dropping
  the conditional texts makes items 8/12/13 approvable.
- **S5-3/S5-4/S5-5 are addressed.** The producers are listed, the `rfl` sentence is corrected, and
  the compaction family's users are named. `StartCompactingServer`/`MainLinked` use
  `NewServer.specCompact` (item 14'), not the family.
- **The apply Draft** is unchanged and still approvable.

## Per-item verdicts

| Item | Verdict |
|---|---|
| 1 `dispatchOk` in place | approvable |
| 2 `dispatchAnswer`/`dispatchResult`/`applyResultIs` | approvable |
| 3 apply vocabulary | approvable |
| 4 A1 record | approvable |
| 5 `kvInv` in place | approvable |
| 6 `reqPropOk` in place | approvable. The commit plan is sound; fix the wording and name `srvReqLogLb_of_rlogLb` (S6-3); restate G4 (S6-2) |
| 7 `crevOf` | approvable |
| 8 dropped (S3-3) | approvable (S-5's law open) |
| 9 `cmpTriple` | approvable |
| 10 `Compaction.specD` | approvable |
| 11 `dispatch`/`Apply.specD` | approvable (S-5's law open) |
| 12 `applyEntryNormal.spec` unchanged | approvable |
| 13 apply loop unchanged | approvable |
| 14 `NewServer.specD` | deferred (Q4) |
| 14' interim `NewServer` texts | approvable once R6-1 says where `specM`'s premise lands in the on arm |
| 15 `Compact.specD` | approvable (F5-2 resolved; Q3 open) |
| 16 | withdrawn |
| 17 snapshot track | the collaborator's; as listed |
| 18 mvcc without `ErrFutureRev` | approvable |
| 19 the ties | **R6-1**: the on arm's tie has no producer; repair by (a) or (b). The `kvCertInv(M)` part is approvable. Bring the Draft's `srvReqFieldsAtD` into line (S6-1); list the positional consumers (S6-4) |
| 20 `srvKVCloserW` | approvable |
| 21 `Apply.specRecD` | approvable |

## Ranking by need of revision

1. **The plan's item list:**
   - R6-1: item 19's on-arm tie, by (a) or (b), and item 14''s sentence;
   - S6-3: item 6's wording;
   - S6-2: G4 and the stale sections;
   - S6-4.
2. **Server Draft** (S6-1):
   - `srvReqFieldsAtD` gains `kvCertInv`, with its docstring;
   - `cmpReach`'s docstring;
   - if (b) is chosen, a `kvTieM` beside it.
3. **Specs Draft:** nothing (F5-2 is done).
4. **Apply Draft:** nothing.

**The first tier is not empty: R6-1 is left.** It is one conjunct whose on-mode instance no
producer makes, and it was introduced by round 4's S4-1 repair. Repair (b) is a definition of
three lines that keeps both `rfl` laws and touches no auth-on text. With R6-1 repaired, I found
nothing else wrong, unprovable or unusable. Round 5's two repairs (F5-1, F5-2) introduce no new
defect.
