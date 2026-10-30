**User-approved 2026-10-30**, with two decisions: `Cluster.Read.spec` is `Cluster.Get.spec` word for word (only the function name differs), and the prophecy is resolved by gokv's `trusted_proph.ResolveBytes` with the returned string (open point 5's second option; no `resolveStr`/`encStr`).

# Candidate: a logically atomic `Cluster.Read` for kvreconf (2026-10-30)

Status: **candidate for the user's sign-off**. Nothing in the repository was edited and nothing
was proved. All references are to `origin/kvreconf-final` unless they say otherwise. Raft's read
API is at `origin/raft-final:interface/Proof/go_etcd_io/raft/v3/InvNode.txt`.

## Open points (for the user)

1. **The coordinator's sketch puts the linearization point in the wrong place.** Its idea was to
   fire the caller's update at the raft confirmation the answer comes from. That does not work.
   `Replica.answer` answers with `r.kv[key]` at the replica's **applied index** `r.index`, and
   `r.index` may be larger than the read index (`kv.go:564`: `if r.index < rs.Index {continue}`,
   then `kv.go:574`: `ch <- r.kv[key]`). If a Put to `key` commits after the confirmation and
   before the answer, the state at the confirmation does not hold the answered value. The
   candidate instead prophesies the **answered value** `v`. It fires the caller's update at the
   first change of the store, from the start of the call on, after which `key` has the value `v`.
   Commits of other operations fire it, by helping, inside `kvr_propAu`. Raft's confirmation is
   not used for linearization at all.
2. **Raft does not change.** The proof uses only the read-index lower bound (`readCtxAfter`,
   `readStateOk_after`), which `Replica.read.spec` already exports as `L0 <+: L`. The persistent
   peek update at the confirmation (`readStateOk_ctx`'s `□ Q`) is not needed. Its `Q` stays
   `True` (`Replica__read.lean:134`).
3. **A Go change in kvreconf (proof-only, no effect at run time).** `Cluster.Read` creates one
   prophecy per call (`primitive.NewProph`). Before it returns, it resolves the prophecy with the
   answer, using a new helper `resolveStr`: one `ResolveU64` per byte, then `ResolveU64(256)` as an
   end marker. The diff is below. Both primitives already have proved specs in Perennial
   (`Perennial/Proof/github_com/goose_lang/primitive/{NewProph,ProphId__ResolveU64}.lean`). Their
   trusted models (`Perennial/TrustedCode/github_com/goose_lang/primitive.lean:61-70`) join
   kvreconf's trust base. That base already holds `RandomUint64` from the same file.
4. **New ghost state (flagged):**
   - a new `RNames` field `rds`, the registry of reads in flight;
   - per call, a saved predicate (the caller's `Φ`) and a `token`;
   - a third conjunct `readReg γr (logHist ops)` of `rkvInvBody`.

   The details are below. The only place where the store's history grows is the first-occurrence
   case of `kvr_propAu` (`ClientAu.lean:172`). There the read slots are stepped. Every other proof
   that opens `rkvInv` carries `readReg` along, since the history does not move there.
5. **Encoding of the prophecy (to choose).** Primitive only has `ResolveU64`/`ResolveBool`. Two
   ways to resolve with a value:
   - one `ResolveU64` per byte plus the end marker 256 (chosen: no new dependency, nothing new to
     trust);
   - gokv's `trusted_proph.ResolveBytes` (one call). This needs a new Go dependency and a spec of
     its trusted model. The model exists, `Perennial/TrustedCode/github_com/mit_pdos/gokv/trusted_proph.lean`,
     but it has no spec: either a Perennial change or a local spec.
6. **Inherited vocabulary.** The statement is `Cluster.Get.spec` word for word. That is
   `run_apply_read` (`ReadAtomic.lean`) with the `sorry` removed. It keeps Get's vocabulary
   (`RNames`, `rkvVal`, `kvrMask`), which names the implementation's ghost state and masks rather
   than an abstract `kvState`. That is a question about Get and Read together and is out of scope
   here. Read follows its sibling, as the principle "in the shape of the closest sibling" asks.

## 1. The spec of `Cluster.Read` (replaces the lower-bound spec)

`Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/Cluster__Read.lean`:

```lean
/- `c.Read(key)` (cluster.go): logically atomic over the store's map, returning `m key`: a read by
read index at random members, retried until one answers. It linearizes at the first moment of the
call at which `key` has the value it returns (a prophecy, `resolveStr`; see the proof). -/
abbrev Cluster.Read.spec : Prop :=
  ∀ (γr : RNames) (vs : List w64) (c : Loc) (key : List w8) (Φ : List w8 → IProp GF),
  (key.length : Int) < 2 ^ 61 →
  {{ isClusterC γr vs c ∗
      AU <{ ∃∃ (x : KVMap), rkvVal γr x }> @ kvrMask, ∅ <{ rkvVal γr x, COMM Φ (x key) }> }}
    (App (Val (c @!! go.GoType.PointerType rClusterTy @!! go!"Read")) (Val #key))
  {{ (res : List w8), RET #res; Φ res }}
```

- **Identical to `Cluster.Get.spec`** (`Spec/.../kvreconf/Cluster__Get.lean`) and to
  `run_apply_read` (`Proof/.../kvreconf/ReadAtomic.lean`). `Run.wp_proof` swaps `run_apply_read`
  for `wp_Read` (`Run.lean:216`), with no other change, and `ReadAtomic.lean` is deleted.
- **One spec per function.** It replaces the lower-bound spec (`kvLb L0 ⊢ ∃ L, kvLb L ∗ …`). That
  spec has no other user: a `git grep` of `Cluster.Read.spec`/`run_apply_read` finds only
  `Cluster__Read.lean`, `Run.lean` and `ReadAtomic.lean`.
- **Strength.** A one-shot update is stronger than `range.md`'s persistent one: give the one-shot
  spec `Φ v := ∃ σ, □ Q σ ∗ ⌜σ key = v⌝`, use the `□ AU` once, and the persistent form follows.
  The converse needs a prophecy at the client. So this is the stronger spec, and the one lintest
  needs.
- **The `key.length < 2^61` premise** is Get's and `Replica.read.spec`'s: the read context's
  encoding (`readCtx`, `kv.go`) needs it. The spec adds no premise.
- **No thread token and no credit in the precondition**, as for Get. The later credits come from
  steps of the body.

### What lintest's `applySpec` needs, and whether this meets it

`lintest.applySpec` (`Proof/.../lintest/Defs.lean:71-75`) is a one-shot logically atomic triple:
`<<{ ∀∀ s, libState s }>> apply i @@ Eapp <<{ ∃∃ s' o, libState s' ∗ ⌜S.M.step s (i,o) = some s'⌝ }>>`.
The output `o` is fixed at the commit. `Run.wp_proof` already turns it, for an `opRead` input,
into exactly the update above, through `kvrAu_of_run` with `(fun s => s) (fun s => s x.Key')`
(`Run.lean:210-219`, the same as the Get branch). It then needs a triple of this exact shape for
`c.Read`, and that is what this spec is. **It meets it**, with no change to lintest.

## 2. The Go change (kvreconf, `examples/kvreconf/cluster.go` and `kv.go`)

```diff
--- a/examples/kvreconf/cluster.go
+++ b/examples/kvreconf/cluster.go
 // Read returns key's value by a read index at a random member, retried at another until one
-// answers (a read has no effect: each attempt is a fresh one).
+// answers (a read has no effect: each attempt is a fresh one). The prophecy p, resolved with the
+// answer (resolveStr), is for the proof only (it tells the proof, at each change of the store,
+// whether the key's value then is the answer: the read's linearization point); it has no effect.
 func (c *Cluster) Read(key string) string {
+	p := primitive.NewProph()
 	for {
 		if v, ok := c.randomMember().read(key, opTimeout); ok {
+			resolveStr(p, v)
 			return v
 		}
 		c.Stats.add(&c.Stats.Retries)
 	}
 }
--- a/examples/kvreconf/kv.go
+++ b/examples/kvreconf/kv.go
+// resolveStr resolves the prophecy p with s: each of its bytes, then 256 (past every byte: the
+// end). For the proofs only; it has no effect.
+func resolveStr(p primitive.ProphId, s string) {
+	for i := 0; i < len(s); i++ {
+		p.ResolveU64(uint64(s[i]))
+	}
+	p.ResolveU64(256)
+}
```

(`cluster.go` imports `github.com/goose-lang/primitive`. `kv.go` already does, for
`RandomUint64`. `primitive@v0.2.2-0.20260212023729-cb7f52217e65`, which `examples/go.mod` pins,
has `NewProph`/`ResolveU64` in `proph.go`.) Then run `etc/goose.py --project kvreconf` again (or
whatever the project's name is in `etc/goose.py`).

## 3. Internal pieces

### `resolveStr` (new)

`Base.lean` (pure):

```lean
/-- A string as `resolveStr` resolves a prophecy with it: its bytes (as `uint64`s), then 256. -/
def encStr (s : List w8) : List val := s.map (fun b => #(W64 (uint.Z b))) ++ [#(W64 256)]

/-- `encStr` is prefix-free: two strings whose encodings both start one list are equal.
(Each byte is `< 256`; `#` is injective on `w64`.) -/
theorem encStr_prefix_inj (a b : List w8) (P : List val) :
  encStr a <+: P → encStr b <+: P → a = b
```

`Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/resolveStr.lean`:

```lean
abbrev resolveStr.spec : Prop :=
  ∀ (p : ProphId) (pvs : List val) (s : List w8),
  {{ proph p pvs }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvreconf.resolveStr)) (Val #p))
      (Val #s))
  {{ RET #(); ∃ pvs', ⌜pvs = encStr s ++ pvs'⌝ ∗ proph p pvs' }}
```

It holds by `ProphId.ResolveU64.spec`
(`Perennial/Spec/github_com/goose_lang/primitive/ProphId__ResolveU64.lean`: `pvs = #x :: pvs'`)
once per iteration, with the loop invariant
`proph p pvs_i ∗ ⌜pvs = (s.take i).map (#·W64) ++ pvs_i⌝`. It needs no premise on `s.length`: a
string of `2^63` bytes or more makes `len` an `AngelicExit`
(`Perennial/Golang/Defn/String.lean:47-50`).

### `Replica.read`, `Replica.answer`: unchanged

`Replica.read.spec` (`kvLb γr L0` in; on `ok`, `∃ L, kvLb γr L ∗ ⌜L0 <+: L ∧ v = kvFold L key⌝`)
and `Replica.answer.spec` stay as they are. This is all the new proof needs from an attempt. The
answer is `key`'s value in a committed history `L` that extends the history `L0` at the call's
start. Where that comes from:
- registration: `kvr_mint_read`, `ClientLemmas.lean:296`, through `readCtx_commit_after`;
- the read-index bound: `readStateOk_after`;
- the history applied: `kvr_readAns_ok`, `ClientLemmas.lean:332`, over `readAns`'s
  `isCommittedLogLb ap` with `i ≤ |ap|`.

### The primitive calls

`NewProph.spec`: `{{True}} NewProph #() {{ (pvs) (p), RET #p; proph p pvs }}`. `ResolveU64.spec`
is as above. Both are proved in Perennial, and `Link` takes them.

## 4. The ghost state and the invariant (new; for the user)

`Defs.lean`:

```lean
structure RNames where
  …
  /-- the reads in flight (`Cluster.Read`): `γΦ ↦ ReadRec` (persistent elements; authority in the
  store's invariant) -/
  rds : GName

/-- A read's record: its key, the store's history when it started, its prophecy's values, and the
name of its caller's token. -/
structure ReadRec where
  key : List w8
  start : List (List w8)
  pvs : List val
  tok : GName

/-- **A read's slot** at the history `H`, its caller's predicate saved at `γΦ`. Either it is still
pending: no history since its start gave `key` the prophesied answer, and it holds the caller's
update (with a later credit, as `opSlot`); or it has fired at a history whose `key` value `v` is
the prophesied answer, and holds `Φ v` until the caller takes it with its token. -/
def readSlot (γr : RNames) (γΦ : GName) (s : ReadRec) (H : List (List w8)) : IProp GF :=
  iprop(∃ Φ : List w8 → IProp GF, savedPredOwn γΦ DFrac.discard Φ ∗ ⌜s.start <+: H⌝ ∗
    ( (⌜∀ H', s.start <+: H' → H' <+: H → ¬ encStr (kvFold H' s.key) <+: s.pvs⌝ ∗ £ 1 ∗
        AU <{ ∃∃ (x : KVMap), rkvVal γr x }> @ kvrMask, ∅ <{ rkvVal γr x, COMM Φ (x s.key) }>)
    ∨ (∃ v, ⌜encStr v <+: s.pvs⌝ ∗ (Φ v ∨ token s.tok)) ))

/-- The registry of the reads in flight, at the history `H`. -/
def readReg (γr : RNames) (H : List (List w8)) : IProp GF :=
  iprop(∃ RD : GMap GName ReadRec, ghostMapAuth γr.rds 1 RD ∗
    [∗map] γΦ ↦ s ∈ RD, readSlot γr γΦ s H)

def rkvInvBody (γr : RNames) : IProp GF :=
  iprop(∃ (ops …) (n …) (Mi …) (RS …) (RMi …) (O …) (U …),
    kvCore γr ops n Mi RS RMi O U ∗ ([∗map] d ↦ γp ∈ O, opSlot γr d γp (logHist ops)) ∗
    readReg γr (logHist ops))
```

`readReg` is its own framed predicate, so the existing proofs only carry it. It is not added to
`kvCore`, whose seven binders every opening destructures. `StartCluster` allocates `rds` with
an empty map: `readReg γr H` holds for any `H` with `RD = ∅`. The `RNames` constructor is used
only there.

### The three lemmas (new, `ReadSlot.lean` or `ClientLemmas.lean`)

1. **Start** (`kvr_read_start`, like `kvr_mint`, `ClientLemmas.lean:196-212`):
   ```lean
   theorem kvr_read_start (γr) (key) (pvs) (Φ) (E) (HE : ↑rkvN ⊆ E) (HE' : kvrMask ⊆ E \ ↑rkvN) :
     ⊢ rkvInv γr -∗ £ 1 -∗
       AU <{ ∃∃ x, rkvVal γr x }> @ kvrMask, ∅ <{ rkvVal γr x, COMM Φ (x key) }> ={E}=∗
       ∃ (γΦ γt : GName) (H0 : List (List w8)),
         γΦ ↪[γr.rds]□ ⟨key, H0, pvs, γt⟩ ∗ savedPredOwn γΦ DFrac.discard Φ ∗ token γt ∗
         kvLb γr H0
   ```
   Open `rkvInv`, with `kvCore` timeless (`>`). Let `H0 := logHist ops`. `kvLb γr H0` comes from
   `ownCommittedOps_get_lb` and `logHist_opsOf` (`Base.lean:375`). Allocate `γΦ` fresh for
   `dom RD` and the token. Then:
   - if `encStr (kvFold H0 key) <+: pvs`, fire the update now. `rkvVal_agree`
     (`ClientLemmas.lean:174`) against the invariant's half gives `x = kvFold H0`. The slot is
     fired with `v := kvFold H0 key`, and the credit is not needed.
   - otherwise the slot is pending. Its condition holds because `H0 <+: H' <+: H0` forces
     `H' = H0`.

   The old slots stay under `▷`, since only the auth is taken out (it is timeless), so this needs
   no step.
2. **Grow** (`readReg_grow`, called in `kvr_propAu`'s first-occurrence case, after the
   operation's own update has fired and `Hv` is at `H ++ [d]`, `ClientAu.lean:192-215`):
   ```lean
   theorem readReg_grow (γr) (H) (d) (E) (HE : kvrMask ⊆ E) :
     ⊢ ghostVar γr.val (1:Qp).half (H ++ [d]) -∗ ▷ readReg γr H ={E}=∗
       ghostVar γr.val (1:Qp).half (H ++ [d]) ∗ ▷ readReg γr (H ++ [d])
   ```
   Take each slot out:
   - a fired slot is unchanged, except `start <+: H ++ [d]`.
   - a pending slot with `encStr (kvFold (H ++ [d]) key) <+: pvs`: take its `£ 1` out of the `▷`
     (it is timeless) and use `lc_fupd_elim_later` on its update. Fire it at
     `x = kvFold (H ++ [d])` (`rkvVal_agree`). The slot is now fired with `v := x key`.
   - any other pending slot stays pending. The condition extends because
     `H' <+: H ++ [d] ↔ H' <+: H ∨ H' = H ++ [d]`.
3. **Take** (`kvr_read_take`, at a step after `resolveStr`):
   ```lean
   theorem kvr_read_take (γr) (γΦ) (s : ReadRec) (Φ) (L) (v) (E) (HE : ↑rkvN ⊆ E) :
     encStr v <+: s.pvs → s.start <+: L → v = kvFold L s.key →
     ⊢ rkvInv γr -∗ γΦ ↪[γr.rds]□ s -∗ savedPredOwn γΦ DFrac.discard Φ -∗ token s.tok -∗
       kvLb γr L ={E}=∗ ▷ Φ v
   ```
   The `▷` is stripped by the step around it, or by a credit, as in `Cluster__do.lean:116-118`.
   - **Pending is impossible.** `kvLb γr L` with the invariant's `ownCommittedOps` gives
     `L <+: logHist ops` (`ownCommittedOps_lb_prefix`, `logHist_le_ops`, `PureLemmas.lean:125`).
     So `H' := L` is in the slot's range, while `encStr (kvFold L key) = encStr v <+: pvs`.
   - **Fired.** `Φ' v' ∨ token` together with the caller's token gives `Φ' v'`, and the
     caller's token goes back in. `encStr_prefix_inj` gives `v' = v`, and the saved predicates
     agree under `▷`.

## 5. The proof of `Cluster.Read` (sketch)

1. Run `p := NewProph()`, which gives `proph p pvs`. Take a credit from a step of the body and
   call `kvr_read_start`. That gives `γΦ ↪□ ⟨key, H0, pvs, γt⟩`, `savedPredOwn γΦ □ Φ`,
   `token γt` and `kvLb γr H0`.
2. Loop invariant: `proph p pvs ∗ token γt ∗ kvLb γr H0` (the rest is persistent). Each attempt
   is `wp_read … H0` (`Replica.read.spec`, unchanged). On `ok = false`: `Stats.add`, then go
   round again (`Cluster__Read.lean`, as today). On `ok = true` there is
   `kvLb γr L ∗ ⌜H0 <+: L ∧ v = kvFold L key⌝`.
3. Call `resolveStr p v`. It gives `⌜pvs = encStr v ++ pvs'⌝`, so `encStr v <+: pvs`.
4. At the next step, `kvr_read_take`, which gives `Φ v`. Return `v`.

**Why it linearizes (the argument the invariant encodes).** The store's history `H` only grows,
and one datum at a time:
- its only update is `rkvVal_update` in `kvr_propAu`'s first-occurrence case (`ClientAu.lean:172`,
  `logHist ops ++ [d]`; `git grep rkvVal_update` finds no other caller);
- a repeated occurrence leaves it (`ClientAu.lean:158`);
- a configuration change leaves it (`logHist_conf`, `ClientAu.lean:44`).

At the call's start the history is `H0`. When the call returns it is some `Hnow`, and
`H0 <+: L <+: Hnow`. So `H` passed through `L`, whose value of `key` is `v`, between the start
and the return. The slot fires the caller's update at the first such history, and the prophecy
says which value to wait for. If the call never returns, the prophecy is never resolved and
nothing is owed.

## 6. Why raft's read API suffices as is

- `readCtx_commit_after` (registration with a committed `l0`, `Q := True`) and
  `readStateOk_after` (`l0.length ≤ idx`) give the lower bound. `readAns`'s
  `isCommittedLogLb ap` with `idx ≤ |ap|` gives the upper bound (answered from a committed
  history). The atomicity comes from kvreconf's own invariant, which sees every change of the
  history, because `ownCommittedOps` is the client's resource (TaDa): raft changes it only
  through kvreconf's updates (`node.Propose`'s and `ProposeConfChange`'s, `ClientAu.lean`).
- `readStateOk_ctx` (`□ Q (opsOf l)` with `|l| = idx`) does not help. Its moment is the
  confirmation's, and the answer's history `ap` may be longer (§ Open point 1). A Q-based design
  would need raft to give `Q` at the applied index, which it does not know. No raft strengthening
  is proposed.

## 7. Alternatives considered

- **Fire at the confirmation, prophesying which confirmation answers** (the sketch). Rejected:
  it gives the wrong output when a write to `key` commits in `(idx, r.index]` (§ 1). Fixing it
  would mean answering from the state at exactly `rs.Index`:
  - either a versioned store in Go;
  - or answering only when `r.index == rs.Index`, and dropping a read otherwise, which loses
    liveness: a follower has often applied past the leader's read index.

  Neither is worth it.
- **Prophesy the answering replica's applied index (`r.index`, one `ResolveU64`).** Rejected. At a
  commit the invariant would have to decide whether the current history is the one of length
  `r.index` in the final log, which is not known yet. The value is what the invariant can compare.
- **gokv's `trusted_proph.ResolveBytes`** (one call). This is open point 5: it adds a Go
  dependency and a spec of a trusted model.
- **A range-style spec (`□ AU … COMM □ Q σ`, post `∃ σ, □ Q σ ∗ ⌜res = σ key⌝`)**, provable
  without a prophecy by firing at every change. Rejected as the spec: it is weaker (a corollary
  of this one, § 1), and lintest's one-shot `applySpec` cannot use it.
- **A lintest change: `applySpec` taking a persistent update for read-only inputs.** The
  prophecy, or a retroactive linearization of read-only operations, would then move into
  lintest's generic theory (`LinTheory.lean`). That theory would need a notion of read-only
  steps (`S.M.step s (i,o) = some s`) and a log of every state. Rejected:
  - it is a disjunction of two applySpec forms in a proved generic spec;
  - it is larger;
  - it needs the weaker spec from the library, where the stronger one is available.
- **Read through the log (as `Get`).** Rejected: it is no longer a read-index read, which is the
  point of `Read`.

## 8. Cost (estimate)

- **Go:** about 10 lines; Goose regenerated for kvreconf.
- **New:**
  - `encStr`, `encStr_prefix_inj`;
  - `resolveStr.{spec,wp_proof}`;
  - `ReadRec`, `readSlot`, `readReg`;
  - three lemmas (about 150-250 lines);
  - a new `Cluster.Read.wp_proof` (about 80 lines).
- **Changed:**
  - `RNames` (+`rds`) and `StartCluster` (allocation);
  - `rkvInvBody` and the six files that destructure it (carry `readReg`);
  - `kvr_propAu` (one `readReg_grow` call in its first-occurrence case);
  - `Run.lean` (`run_apply_read` becomes `wp_Read`);
  - kvreconf's `Link` (with `wp_NewProph`, `wp_ResolveU64`, `wp_resolveStr`);
  - `ReadAtomic.lean` deleted.
- **Trust base:** adds primitive's `NewProph`/`ResolveU64` models (Perennial
  `TrustedCode/github_com/goose_lang/primitive.lean`) and their proved specs. It removes the
  `sorry` of `run_apply_read`.
