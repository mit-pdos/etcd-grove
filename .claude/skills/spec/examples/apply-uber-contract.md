# `apply.Apply` over its interface's contract; the on server's uber-applier contracts (2026-10-30)

etcd's `apply.Apply(lg, e, uberApply, w, shouldApplyV3)` (`apply/apply.go:27-49`) decodes an entry,
reads its id, asks `w.IsRegistered(id)`, and calls `uberApply.Apply(wrapper, shouldApplyV3)` through
the `UberApplier` interface; it knows nothing of the applier's contract. Step 6 of the auth-mode
merge. Three spec-reviewer rounds, then the user approved candidate 3 as written.

## The first version (the repository's specs at the time)

Three triples of the same function, each with its own copy of the proof:
- `apply.Apply.spec`, over `applierFor ua E` (the recorded-state triple of the uber-applier);
- `kvSpecL`, over `uberKVL` (a KV entry, the verdict at the latest state);
- `adminSpecL`, over `uberAuthStepsL` (an admin entry).

The server's `applyEntryNormal` had a second spec with auth on, whose proof took 14 hypotheses that
are not `.spec`s: 12 interface-method specs, used only to build `uberKVL`/`uberAuthStepsL` inside
the proof, plus `kvSpecL` and an admin variant. So it could not be linked over `.spec`s.

## The critiques, in order (spec reviewer; the user approved the result)

1. **Round 1.** Candidate 1 stored the *base* applier's predicates (`uberKVL`) in the server. The
   uber-applier's own triples are what `apply.Apply` calls, and they come from separate proofs
   (`uberApplier.Apply.wp_kvL`), so storing the base level left those proofs as hypotheses again.
   The recorded-state triple also had no source.
   - Changed: store the uber-applier's own contracts.
   - Changed: one rule for both modes, **whoever constructs the uber-applier establishes its
     contract**.
2. **Round 2.** The stored row was tied to one `ua`, but `applySnapshot` replaces the
   uber-applier. The server's own constructor was missing, and the call was written as a
   placeholder (`interface.call`).
   - Changed: the row quantifies over every `ua` with its base fact (`srvUberBase s ua E -∗ …`).
   - Changed: the call is written as `waitOk` writes its method (`∃ ui, ⌜ua = .ok ui⌝ ∗ □ ∀ …,
     {{…}} methods ui.ty "Apply" ui.v …`), which also rules out a nil interface.
3. **Round 3.**
   - Quantify the row over the environment too (the snapshot path rebuilds it at another `E`).
   - Use the simpler, equivalent waiter fact.
   - Put the row in the mode-indexed `srvKVInvsM true`, so the off equalities stay `rfl`.
   - The kit also needs `applierV3backend.Apply.spec`.
   - List every trusted statement that changes, including the chain that reads the changed
     definition.

## The approved spec

```lean
abbrev apply.Apply.spec : Prop :=
  ∀ (lg e : Loc) (m : EntryModel) (ua w : GoInterface) (v3 : Bool) (rq : IRRModel) (id : w64)
    (RD : IProp GF) (K G : Option GName → w64 → IProp GF) (ot : Option GName)
    (P : IProp GF) (Q : Bool → Loc → IProp GF),
  {{ isPkgInit … apply ∗ waitOk w RD K G ∗ RD ∗ K ot id ∗ ⌜lg ≠ null⌝ ∗ entryAt e m ∗
      ⌜apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id⌝ ∗
      (∃ ui : GoInterfaceOk, ⌜ua = GoInterface.ok ui⌝ ∗
        □ ∀ (r : Loc) (sk : Bool),
          {{ apply.irrWrapperIs r rq sk ∗ ⌜sk = true → rq.txn.isSome = true⌝ ∗ P }}
            (App (App (Val #(methods ui.ty go!"Apply" ui.v)) (Val #r)) (Val #v3))
          {{ (ar : Loc), RET #ar; Q sk ar }}) ∗ P }}
    Apply #lg #e #ua #w #v3
  {{ (ar : Loc) (id' : w64), RET (PairV #ar #id'); RD ∗ ⌜id' = id⌝ ∗
      ((∃ sk : Bool, Q sk ar ∗ (⌜sk = false⌝ ∨ G ot id)) ∨
       (⌜ar = null ∧ apply.noSideEffect rq = true⌝ ∗ G ot id ∗ P)) }}
```

The three old forms are corollaries at the uber-applier's three contracts (`spec_rec`, `wp_kvL`,
`wp_adminL`), with no second proof of the Go code.

With auth on, `NewServer` builds `srvUberOn s` once, from a kit that is `True` with auth off. The
row holds, for every `E` with auth on and every `ua` with `srvUberBase s ua E`, the KV and admin
contracts in the method form above. `applyEntryNormal` reads it and has one spec.

## What it teaches

- **A function that calls through an interface gets one spec, parametric in the method's
  contract** (its pre `P`, post `Q`, persistent), not one spec per implementation's contract.
- **Whoever constructs the object establishes its methods' contracts**, once, where the
  construction has the specs. A consumer that builds them takes non-`.spec` hypotheses and cannot
  be linked.
- **Store the contract at the level the consumer calls** (the uber-applier's, not its base
  applier's), and for every object the field may come to hold (`∀ ua`, `∀ E`), not only the
  first one.
- Implementation found a simpler route for the off mode (the caller takes the concrete method's
  `.spec` as a callee, since `applierFor` pins the type), with fewer trusted changes. It was
  reported to the user as a deviation, not adopted silently.
