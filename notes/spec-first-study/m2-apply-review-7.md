# M2 apply side, Draft: review round 7 (2026-10-30, narrow)

Reviewed: `m2-apply` at `87f520eaac` ("round 6 and its repair"). Scope: round 6's repair only.
- R6-1: `kvTieM` in `srvReqFieldsAtM`'s auth-on arm.
- S6-1: `srvReqFieldsAtD` with `kvCertInv`.
- Plan items 6 and 19, G4, and "What `applyAll`/`run` need".

Judged under the in-place convention (the user's Q6 (a)). "The off texts mean today's by laws" is not
re-raised.

- **Checked:** `etc/lean-check.py -q -a` on `M2ApplyDraft.lean` (the server Draft): 0 errors.
- **Go:** I read no Go code for this round. I found no Go bug; nothing goes to `issues/`.

## R6-1's repair: `kvTieM`, sound

**The definition** (`M2ApplyDraft.lean:545-551`):
- `kvTieM on cmp E` is `cmp = E.cmp` when `on = false`, and `True` when `on = true`.
- `kvTieM_off` holds by `rfl`.
- So when `srvReqFieldsAtM` carries `⌜kvTieM on ρ.kv.cmp E⌝` at the place where `srvReqFieldsAt`
  carries `⌜ρ.kv.cmp = E.cmp⌝`, `srvReqFieldsAtM_false` (`ReqOn.lean:400`) stays `rfl`. It
  reduces the same way `kvCertInvM false` does (`ServerOn.lean:241-245`).

**The producer.** `start.specOn` proves `True`. R6-1's gap is closed. The off producer (`start`'s
`srvReqBuilt`/`srvKVInvs` route) is unchanged.

**Consumers of the tie. Every one is in the off arm or vacuous in the on arm:**
- **`EtcdServer.Compact`** reads `isServerReq`, which is off by definition
  (`InvProposer.lean:432-433`, `⌜E.authOn = false⌝`). Item 15's `Compact.specD` is stated over it.
- **`compactableOk_server`** (`CompactEnv.lean:71-77`) reads `isServerReqC` today and
  `isServerReq` after the switch. Both are off.
- **The request path's proposers with auth on** read no tie:
  - `reqPropOkM true` is `reqPropOkOn` (`ReqOn.lean:579-583`), and `reqPropOkOn`'s four cases all
    require `plainReq` or `adminPropOk` (`ProposeOn.lean:340-360`). So an auth-on proposer cannot
    present a compaction form.
  - Item 6 changes only `reqPropOk`, which is the off arm of `reqPropOkM`.
  - `kv_prop_au_M`'s on arm goes through `kv_prop_au_on` and never mentions `γk.cmp`
    (`ReqOn.lean:687-704`).
- **The off proposer's commit needs no tie either.** `reqPropOk γk`'s compaction form is gated by
  `γk.cmp = true`, and `kvInv γk` is read at `γk.cmp`: both come from the same names.
- **The apply side's derivation (item 8)** reads the tie through `srvKVInvs`, which is the off arm
  of `srvKVInvsM` (`ServerOn.lean:384-387`). In the on arm, `kvInvOn`'s `plainLogOn` makes
  `cmpAdmit` vacuous (round 6).
- **Put/Range/Txn** are written over `srvReqFieldsAtM` for both modes. They carry the tie but
  neither proposes nor admits a compaction.

**The scope** "auth on implies compaction off" holds, and it is stated where it is used:
`NewServer.specM` keeps `AutoCompactionRetention' = 0` and `E₀.cmp = false` for both values of
`on` (`Spec/…/NewServer.lean:456-459`).

**Does `NewServer.specM`'s premise `ρ.rd.kv.cmp = false` still have a use?**
- **Yes, in its off arm.** `srvBuiltG false` carries `srvKVInvs`, whose item-19 tie
  `ρ.rd.kv.cmp = E.cmp` is made from this premise, `E₀.cmp = false` and `envAgree`.
  `NewServer.spec` is the off instance (`spec_of_specM`, `NewServer.lean:422`), so the premise is
  load-bearing there.
- **In the on arm, nothing reads it:**
  - `kvInvOn`, `kvCertInvOn` and `srvKVInvsOn` do not mention `KVNames.cmp`;
  - `kvTieM true` is `True`.
- So the plan's sentence "used only by its allocation" (item 19, `m2-apply-plan.md:531-533`) is
  wrong on both counts:
  - the off arm uses it, for the post's tie;
  - the allocation of `kvInvM on` is the caller's (`#Hkvinv` in the precondition), not
    `NewServer`'s.
  - This is second tier (S7-1).

**Verdict on R6-1:** resolved. The repair introduces no new defect.

## S6-1: `srvReqFieldsAtD` with `kvCertInv`: done

- `kvCertInv ρ.raft ρ.kv` now sits beside `kvInvD` (`M2ApplyDraft.lean:522`).
- The off law is `⊣⊢ srvReqFieldsAt … ∗ kvCertInv …`, and it checks.
- Both sides are persistent, so the separating conjunction loses nothing.
- `start` produces the extra conjunct from `srvKVInvs`, as round 6 found
  (`EtcdServer__start.lean:452-480`; `InvApplier.lean:333`).
- `kvCertInv` is not already elsewhere in `isServerReq` (`InvProposer.lean:432-433`), so it is no
  duplicate.
- `cmpReach`'s docstring now names the route (`:462-465`).

## Item 6 (the commit step), G4, "What `applyAll`/`run` need"

- **Item 6** now says that the lemma runs at the caller's `⊤` and the update at `⊤ \ srvRaftN`, and
  it names the route. I checked the three lemmas:
  - `kv_cert_read`: `KVLemmas.lean:766`;
  - `srvReqLogLb_of_rlogLb`: `SrvRaftLog.lean:1025`, mask `⊇ srvRaftN`, consumes
    `srvRaftLogInv`;
  - `srvReqLogLb_prefix`: `SrvRaftLog.lean:1015`, no mask.
  - All three are as described.
  - Still missing from item 6: S6-3's third point, the internal signature change. `kv_prop_au` and
    `kv_prop_au_M` gain `kvCertInv(M)` and `srvRaftLogInv` arguments, and their mask premise grows
    from `↑kvN ⊆ E` (`ReqOn.lean:668`) to `kvN`, `kvcN` and `srvRaftN`. These are internal
    lemmas, so this is second tier (S7-2).
- **G4** is restated and the superseded clauses are marked. Approvable.
- **"What `applyAll`/`run` need"** is marked superseded by items 8/12/13. Approvable.

## First tier

**Nothing is left in the first tier.** R6-1 is resolved, S6-1's change is sound, and I found nothing
wrong, unprovable or unusable by a caller in what the repair touched.

## Second tier

### S7-1. Item 19's sentence on `NewServer.specM`'s premise

- **Principle:** Clarity. The approval reads this sentence.
- **Restatement:** "`NewServer.specM`'s premise `ρ.rd.kv.cmp = false` makes the off arm's tie, in
  `srvBuiltG false`'s `srvKVInvs`, which `NewServer.spec` inherits; nothing reads it in the on arm."
- Optionally weaken the premise to `on = false → ρ.rd.kv.cmp = false`. Keeping it unconditional
  costs an auth-on caller nothing, since it picks the `KVNames` literal itself.

### S7-2. Item 6: the lemma signatures (S6-3's third point, carried)

- Add: "`kv_prop_au`/`kv_prop_au_M` take `kvCertInv(M)` and `srvRaftLogInv`; mask `kvN`, `kvcN`,
  `srvRaftN ⊆ E`; the only caller passes `⊤` and holds `#HrLog`."

### S7-3. `kvTieM`'s docstring and the M copy's text

- **The docstring's argument is wrong.** `M2ApplyDraft.lean:543` says
  "`srvReqFieldsAtM on` carries `kvTieM on γk E`". The signature takes a `Bool`; it should read
  `kvTieM on ρ.kv.cmp E` (the plan has `γk.cmp`).
- **The M copy's text is only prose.** The redefined `srvReqFieldsAtM`, with `kvCertInvM on ρ.raft
  ρ.kv srvAuthSt0` and `⌜kvTieM on ρ.kv.cmp E⌝` beside `kvInvM`, has no drafted text.
  - Under the convention a redefined definition is drafted as `…D`.
  - Its `rfl` law is evidently true. But the user approves texts, and this one is the merged
    request path's (Put, Range, Txn).
  - A `srvReqFieldsAtMD` with `srvReqFieldsAtMD false = srvReqFieldsAtD` by `rfl` would make Lean
    check that claim.
- **Positional consumers in the on family.** The new pure conjunct and `kvCertInvM` shift them too.
  `ReadOn.lean:120`'s pattern ends in `-` (round 6's S6-4), but the on-family destructurings of
  `srvReqFieldsAtM` should go on item 19's list with the off ones.

### S7-4. The plan's "Still open" (stale, from S6-2)

- The last line of `m2-apply-plan.md` still lists S3-3 as open. Items 8/12/13 have adopted it.
- Restate it as "S3-3 adopted (item 8); its lemma is a proof obligation", or drop it.

### Carried

- S-5: the law `kbCmpM E.γ.kb ↔ E.cmp`.
- S-2'/G2 (Q3).
- The storage side's S4: `compactableOk_server`'s views versus `NewServer.wp_proofCompact` running
  before `start`. Uncertain and outside these targets.

## What is good

- **`kvTieM` is the minimal fix.** It is three lines, keeps both `rfl` laws and touches no auth-on
  text. Its on arm is `True` exactly where every auth-on consumer is vacuous: `reqPropOkOn`
  requires `plainReq`, and `plainLogOn` excludes a compaction.
- **S6-1 brings the Draft into line with item 19**, with an off law that Lean checks.
- **Item 6 and G4 now agree** and name the lemmas that exist.

## Per-item verdicts (touched items only)

| Item | Verdict |
|---|---|
| 6 `reqPropOk` in place | approvable; add the internal signatures (S7-2) |
| 14' interim `NewServer` texts | approvable; restate the premise's sentence (S7-1) |
| 19 the ties | approvable; R6-1 resolved; fix the docstring and draft the M copy's text (S7-3) |
| G4 | approvable |
| "What `applyAll`/`run` need" | approvable (marked superseded) |

## Ranking by need of revision

1. **The plan's item list:** S7-1 (item 19's sentence), S7-2 (item 6), S7-4 ("Still open").
2. **Server Draft:** S7-3 (`kvTieM`'s docstring; optionally a `srvReqFieldsAtMD`).
3. **Specs Draft and apply Draft:** not touched by the repair; nothing.

**The first tier is empty.** By the plan's rule, the review rounds end here. What remains is
second-tier wording and one optional drafted text, which can go into the approval batch (Q5).
