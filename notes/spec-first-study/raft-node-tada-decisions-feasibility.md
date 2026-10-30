# TaDa conf-change decisions instead of a fixed decoder: feasibility

Read at HEAD `d9cdd1e4e1` (paths under `Proof/go_etcd_io/raft/v3/`).

## Verdict

**Feasible with changes. Nothing in the safety argument needs to change; what has to change is how the facts are represented.** The protocol proof never folds the decoder over a prefix that has an undecided conf entry, meaning neither (a) nor (b). Every fold is over one of three kinds of prefix:
- a node's configuration-index prefix `full.take cidx`. Every conf entry in it was taken by `applyConf` or rejected at `advance`, so a node decided it.
- a candidate's `take commit`. Past `cidx` it holds no conf entries.
- a snapshot prefix. It ends at or below its creator's `applied ≤ cidx`.

The work is to move `CfgAt` and the fold from a pure, fixed `dec` to a monotone ghost map.

## Where the fold is applied

1. **The node's own configuration.**
   - `RInv.cfg : cfgFold dec c0 (r.full.take r.cidx) = some r.cfg` (Protocol/StepRInv.lean:248), with `applied ≤ cidx ≤ commit` (:244-245).
   - `cidx` moves only in three places:
     - `applyConf` (Protocol/StepR.lean:437-447): the decision `dec (full.take k) e = some (.apply op)` (:443), entry `k < commit`.
     - `advance` (:410-415): `NoUndecConfIn` requires recorded *rejects* (:113-116).
     - `applySnap` (:422-432).
   - Commit never touches `cfg`. Between a conf entry's commit and its application, the node keeps its old configuration. Its index stays below the entry: at most one conf entry is past it at a leader (I3, StepRInv.lean:249, `leader_drop_cidx`), and at a commit fact's committer (`ConfI1`, Protocol/Ghost.lean ~2527).
   - These are decided prefixes: the client hands over the decision at `ApplyConfChange` (`DynCCPreOp`, ApiVocab.lean:342) and at `Advance`.
   - Purpose: every safety argument reads the configuration from here.
2. **The candidate's prefix.**
   - `RInv.cand_cfg` (StepRInv.lean:942-947) folds `take commit`. The campaign guard `NoConfIn applied commit` (StepR.lean:159; raft's `hasUnappliedConfChanges`) means no conf entry lies past `cidx`.
   - The campaign records this prefix in `isCampK` (Ghost.lean:773-779) and the winner records its configuration in `isWinCore` (:881-886).
   - Used for election safety (`win_fresh`, LeaderCompleteness.lean:1200-1290) and leader completeness (`lc_core`, `lc_far_older` :521-547, :603-633).
   - Committed, and decided wherever it holds a conf entry.
3. **The committer's prefix** (`dynEnv`, Protocol/GhostState.lean:152-165, `CfgAt ((fpR++log).take a)` with `a ≤ commit`).
   - It is recorded in `cqAt` (Ghost.lean:2522-2530, together with `isCommitted (G.take a)`).
   - Each conf entry below `a` has a witness `cqAt` whose own index is just before that entry (`WitOk`). So the commit of a not-yet-applied conf entry is argued at the *previous* configuration's decided prefix.
   - Used for commit and leader completeness (`lc_core` far cases), and for read-index quorum overlap (`rqRecOk_confirm`, ReadIndex.lean:536-612).
4. **Snapshot prefixes.**
   - `snapRestore`'s `Adm fp' cs'` (StepR.lean:317), `applySnap`'s `Adm (fp.take j)` (:427), and the certificate's "∀ recorded full prefix `fp` with `FullOk sid fp`" (`raftSnapCert`, Ghost.lean:1579-1583).
   - Also `snapAtOk` (:1555-1558), `SnapAtPure` (InvApi.lean:1401), `RNMode.foldCfg` (InvRawnodeReady.lean:1069-1070), RawNode__Advance.lean:509/556, StepGhostMode.lean:716, raft__Step/Base.lean:520, and `snapshotCert_make` (SnapsMade.lean:137, 198-216).
   - `FullOk sid fp` with a committed `sid` pins `fp` to the committed prefix (log matching, `full_take_eq`). The creator has applied up to `sid`, so these prefixes are decided.
   - Purpose: A3, a snapshot's `ConfState` is its prefix's configuration.
5. **Uncommitted logs.**
   - The leader's and follower's logs, `propBatch`/`propose` (StepR.lean:124, 281), `appAccept`, `ConfI1`/`ConfI3` and `confCount`: none of them fold. They only count conf entries syntactically.
   - `logRecs` appears only as a premise that ties `fp` to the committed log.
   - `FullOk` is a syntactic shape fact.

## Is `adj` needed for undecided prefixes?

No.
- `DynCfg.adj` (Ghost.lean:173-176) is used only through `CfgAt.overlap_adj` (:534-545). Its callers are LeaderCompleteness.lean:547, 633, 1232, 1254, 1288 and ReadIndex.lean:560, 612.
- Every caller passes two `CfgAt` facts, so both folds are `some`, over committed prefixes `P1 <+: P2`.
- The "far" cases conclude from `confCount` and I1 alone (`far_older`/`far_newer`).
- `fold_adjacent` (Protocol/CfgOverlap.lean:372) is proved for an arbitrary `dec`, so it holds as well for "look up the recorded map".

## Changes needed

1. **Replace `RaftNames.reDyn : Option (… → DynCfg)`** (74 occurrences in 19 files) with the name of an agreeing persistent map `idx ↦ CCDecision` and the initial configuration `c0`. Key the map by index, not by entry: committed entries are unique per index, and a decision is recorded only with a committed prefix. For the fold, define `decOf m : CCDec := fun pre _ => m !! pre.length`.
2. **Make `CfgAt` a persistent Iris proposition:** `∃ m, decLb γ m ∗ ⌜cfgFold (decOf m) c0 P = some c⌝`. Alternatively, keep it pure over an explicit `m` and carry `decLb` beside it. Two lemmas are new:
   - `fold_mono`: a fold that is `some` under `m ⊆ m'` is unchanged.
   - agreement of two lower bounds.

   Together they rebuild `overlap_adj` as an Iris lemma (combine `m1 ∪ m2`).

   The edits are mechanical but touch every `⌜… CfgAt …⌝`: about 60 sites in Ghost (28), LeaderCompleteness (13), Refinement (9), ReadIndex (6), GhostState and RefinementDyn.
3. **Parameterise `StepR`/`RInv`/`AdmFold`** by the node's latest witnessed map (`decOf m`), with monotonicity in `m`. Today `StepR.mono` is over `Adm` only.
4. **Rework the API vocabulary.** `ConfRule`/`ConfRule.toDec`/`Membership.fold r c0` (ConfRule.lean, ConfRuleDec.lean, SnapsMade.lean) and the `dec` that `RestartNode.lean:276`/`RawNode__Bootstrap.lean:536` choose become the client's map and its laws. The client's view of the committed operations (`opsOfRule`) becomes the fold of the recorded decisions.

## Who holds the permission, and can the first applier get the decision without raft?

**Who holds it.** The client, for every index. The token family `decTok γ i` is allocated with the cluster (`StartNode`/`Bootstrap`), independent of who proposed the entry. That covers raft's automatic leave entries (`RaftLeave`): the client holds index `i`'s token whether or not it proposed the entry. The bootstrap log's conf entries must be recorded at allocation, because `RInv_init` (StepRInv.lean:322-330) folds `L` at once.

**The client's laws:**
- `decTok i ⊢ |==> decided i d`, guarded by the committed prefix (`isCommitted (L++[e])`, `L.length = i`).
- `decided i d ∗ decided i d' ⊢ ⌜d = d'⌝`.

**No raft code involved.** The first applier gets the decision through the client's own invariant, for example the out-of-band agreement. Raft's proofs consume only `decided` (persistent), as premises of `ApplyConfChange` (`DynCCPreOp`'s `dec … = some (.apply op')` becomes `decided k (.apply op')`) and of `Advance` (the rejects). Raft's ghost steps never write the map.

**Validity.** Validity (`ConfRule.Ok`/`clamp`) can stay the fold's job, with an invalid change folding to `none` or being clamped to reject. Or the client can be required to apply only changes valid at the decided prefix's configuration, as `DynCCPreOp` already demands (`ccStepB op' cfg = some cs'`).

**Not checked:** whether `ConfRule.Ok`'s validity side condition should become a law of recording or stay a premise at `ApplyConfChange`. That is a design choice for the user.
