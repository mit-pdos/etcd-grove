# The server's auth component: a sealed slot in place of mode twins (2026-11-04)

**Kind:** a package-internal API: a slot, with predicates and laws, that replaces a mode index
threaded through about 175 definitions and 14 twin theorems. Frozen by the user, candidate 3, after
two spec-reviewer rounds. Code: `Proof/go_etcd_io/etcd/server/v3/etcdserver/AuthComp.lean`.
Decision: `notes/decisions.md`, "The auth component".

## First version (candidate 1)

`AuthC := off | on γa`, sealed predicates `acRes` (the row's auth part), `acInv`, `acTok`, `acPub`,
`acBkts`, `acImg`, `acOpenQ`, `acModesOk`, `acRead`, `acSnapOk`, and laws for each divergence point
of the twins. The claim was that only `applyEntryNormal`'s data branch diverges in the KV model and
the applier contract, so that branch alone would keep two cases. The admin, Authenticate and boot
laws were shapes ("the existential is fixed by elaboration").

## Critiques (two spec-reviewer rounds) and what they changed

1. **A law false in its trivial instance**: `acSnapOk_intro`'s off case took its fact from the kit,
   but the off kit is `True`; off's fact sits in a separate conjunct. → The off value of a slot
   predicate is defined from where the off proof really gets its fact (`acSnapKit .off :=
   authRecoverOk`), with a bridge law from today's conjuncts.
2. **A law with no client, and false besides** (`acRes_recovered`). → Deferred to the stage whose
   client needs it.
3. **The divergence map was drawn too narrowly**: the model step at the top, and the replayed
   branch with its admin case below `c₀`, also diverge. → The two-case law covers the whole entry.
4. **Divergence points the slot missed** (the lessor premise, the receipt and its bound, the
   compactor's restriction, the window's side condition) and **containers not inventoried**. →
   Added as slot predicates, or listed for stage 2.
5. **Shapes cannot be frozen, and an elimination law that exposed the slot's interior** (the
   history `hs`). → Replaced by opening laws (`acRes_on`, `⊣⊢` today's definition), confined to
   the one two-case law, and marked as a departure until the single model.
6. **Pure pieces sealed although clients outside read them** (`acBkts`, `acOpenQ`). → Made public.
7. (Round 2) **A gate the plan itself could not pass**: containers that differ in the model cannot
   be rewritten through a resource slot. → The allow file names them until stage 3.

## The approved spec

Candidate 3 is what `AuthComp.lean` states: its header and docstrings, and the laws in the order
of the twins' divergence points.

Principles exercised: PRINCIPLES' slot convention (a hub names a subsystem through sealed slots and
laws); a law's trivial instance must be checked as carefully as the real one; a spec in shapes is
not a candidate; map the clients' divergence points before stating the laws.
