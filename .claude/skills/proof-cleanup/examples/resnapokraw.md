# raft's `RaftNames.reSnapOkRaw` (2026-11-15)

**Status:** picked by the user as an example of the cleanup this skill should do; not carried out yet
(other raft work was about to land and would conflict). Line numbers are at `origin/lean` `dd068e790f`.

## The kind

A judgement on the proofs as they stand, not on how they got there. Two findings, each enough on its
own:

1. **Predicate injection.** The library's ghost state takes a client-supplied predicate as a
   parameter and promises it of what it hands out (HOCAP style): the library carries a property it
   does not understand, and every client must fix its property up front, at allocation. We don't
   want specs of this shape. The preferred shape is client-owned ghost state: the library gives the
   client an exclusive resource for what it has put in (here, the snapshots it made), with a
   logically atomic or ghost update to add to it, and guarantees only that what comes out was put
   in. Each client keeps whatever property it needs in its own invariant, next to the resource.
2. **Unnecessary.** In the current proofs nothing needs the parameter: every result goes through
   without it. The client-owned form is already there and every client uses it; every remaining use
   of the parameter pins it to `True`, and the code that would give it a real value has no users.

The second finding is what makes it a deletion rather than a redesign. Without it (an injected
predicate some proof still relies on), propose the redesign: it is a spec change.

**History is context, not a reason.** That the field is left over from an earlier design is not
why it goes; it goes because nothing needs it now. Read the history (`notes/decisions.md`, the
plan, the commits that added it) for why it was chosen and what replaced it, so the cleanup does not
reintroduce a problem the original design solved.

## What is there

Raft's ghost names carry the application's relation between a committed log prefix and a snapshot's
data bytes, fixed when the cluster is allocated (`Proof/go_etcd_io/raft/v3/Protocol/Ghost.lean:373`):

```lean
  reSnapOkRaw : List BootEntry → List w8 → Prop
```

read as `RaftNames.reSnapOk γ L d` (`Ghost.lean:536`) inside the data certificate a snapshot carries
from the node that took it to the node that installs it (`Ghost.lean:1952`):

```lean
def snapDataOk (γ : RaftNames) (i : w64) (d : List w8) : IProp GF :=
  iprop(∃ L : List EntryM, isCommitted γ L ∗ ⌜L.length = uint.nat i ∧ γ.reSnapOk L d⌝ ∗
    snapRegOk γ i d)
```

Beside it, the client-owned form: the client owns a registry of the snapshots it made
(`ownSnapsMade γ S`, `snapMade γ s`, `snapMade_elem`, which gives `s ∈ S`) and registers each one with
a ghost update (`snapshotCert_make`, `InvNodeRule.lean:436`: `ownSnapsMade γ S ={E}=∗ ownSnapsMade γ
(S ++ [r]) ∗ snapshotCert …`, any data). Raft guarantees that a snapshot it hands out is one the
client registered (`snapRegOk` in `snapDataOk`).

## Why nothing needs it

Every client states its property of its snapshots on its own side, in its invariant over the
registry:

- etcd's server: `srvSnapsReg cl := ∃ S, ownSnapsMade cl S ∗ ⌜∀ r ∈ S, r.data = []⌝`
  (`Proof/go_etcd_io/etcd/server/v3/etcdserver/SrvRaftLog.lean:753`);
- the kv examples: `kvSnapOk` (`examples/raft/kv/Base.lean:470`, `kvreconf/Base.lean:472`), in their
  invariant over the registry (`kv/Defs.lean:338`).

And every use of the field is trivial or dead:

- the client API's names, `DecNames` (`InvApi.lean:171`), *require* `∀ L d, γ.raft.reSnapOkRaw L d`;
- `SnapValidCert.lean:142`, `:176` take the same all-true premise;
- `Ghost.lean:1980` is a lemma for a cluster that "admits every data";
- the only definitions that set it to a real predicate, `StaticNames` with `sokOf`/`reSnapOk_sokOf`
  (`InvApi.lean:884-900`), have no users in `Proof/`, `Spec/` or the parts;
- the allocation lemmas just pass it through (`Protocol/Facts.lean:1382`, `:1591`, `:1657`, the `sok`
  parameter).

(Context, from the history: the injected form came first, D22 S-r, 2026-10-21; the registry replaced
it in stages U2 and U4a of `notes/raft-unified-plan.md`, commits `2aa8429145` and `24139aa764`. The
registry also lets raft promise a snapshot is one the client made, which the injected form could
not.)

## How it was found

Not by an unused-declaration search: the field is used in about a dozen places. Read each use in
the current proofs:

1. Grep for the field and classify every hit: a premise pinning it to `True`, a pass-through, or a
   definition with no users. If every hit is one of these, the field constrains nothing.
2. For a definition that gives it a real value, grep its names outside their own file: no users.
3. For the property the field would carry, find where each client states it instead. If some client
   still needs the injected form, the field is necessary and this is a redesign, not a deletion.
4. A docstring naming another mechanism (here the registry's, next to the field in `RaftNames`) is a
   lead to steps 1-3, not evidence by itself.

## The cleanup

- `Protocol/Ghost.lean`: delete the field, `RaftNames.reSnapOk`, the `reSnapOk L d` conjunct of
  `snapDataOk` (leaving `∃ L, isCommitted γ L ∗ ⌜L.length = i⌝ ∗ snapRegOk γ i d`), and the
  every-data lemma at `:1977`.
- `Protocol/Facts.lean`: drop the `sok` parameter and its conjunct from the allocation lemmas.
- `InvApi.lean`: drop the conjunct of `DecNames` and the one at `:1504`; delete `StaticNames`,
  `sokOf`, `reSnapOk_sokOf`.
- `SnapValidCert.lean`: drop the two premises.

Considered at the same time, and decided separately: making the registry mandatory (`reSnapReg :
GName` instead of `Option GName`), which would remove the `reSnapReg = none` branches only the dead
static mode needed. First check who still passes `none`.

## Checks and cost

- `Protocol/Ghost.lean` is near the bottom of raft: `etc/importers.py --count` gives 4,728 modules
  (703k lines), essentially a full build. Schedule it when the raft proof is not being changed
  elsewhere, and land it quickly.
- The fingerprint diff touches definitions the exported results reach through the cluster names,
  only by removing a field nothing constrains. That is a change to a definition under a top-level
  statement, so present it to the user as such; it does not change what any result says.
- No axiom or `sorry` is added or removed.
