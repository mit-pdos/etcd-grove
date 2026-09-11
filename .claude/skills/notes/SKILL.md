---
name: notes
description: Record this session's work in the repo's persistent notes/ directory so a fresh agent can pick it up. Use at the end of any session that did real work on the proof, when the Stop hook asks for notes, or when the user says "write this up", "update the notes", or "/notes".
---

# Update the persistent notes

`notes/` is this repo's committed, cross-session memory. Your job is to leave
it in a state where **an agent with no conversation history can continue the
work**. See `notes/README.md` for the full contract.

Work through the steps below in order. Skip a step only when you can say why it
does not apply — not because it is more effort.

## 1. Orient

Read `notes/STATUS.md` and `notes/README.md` if they are not already in
context. Check what today's date is and whether
`notes/journal/YYYY-MM-DD.md` exists yet.

## 2. Update `notes/STATUS.md` — always

Rewrite the parts that are now wrong. Specifically:

- **Where things stand** — did anything actually get proved, refactored, or
  broken? Update the per-file descriptions if they no longer match.
- **In flight** — what is half-done right now, and what state is it in (does it
  build? does it have admits?). Be concrete: an agent reading this should be
  able to resume mid-lemma.
- **Next steps** — remove what got done, add what this session revealed. If you
  claimed a next step, say so.
- **Last updated** — today's date.

Do not just append. Stale text in `STATUS.md` is worse than no text, because it
gets trusted.

Keep the file under ~150 lines; push detail into `topics/`.

## 3. Append to today's journal

`notes/journal/YYYY-MM-DD.md`, using the template in
`notes/journal/README.md`. New `##` section per session; never rewrite earlier
entries.

The **dead ends** bullet is the one people skip and the one that pays. What did
you try that did not work, and why? An approach that failed for a subtle reason
saves the next agent hours.

## 4. Capture what outlives the session

Ask yourself each of these and act on any that is a yes:

- **Did something non-obvious cost you time?** → add an entry to
  `notes/gotchas.md`. One short paragraph: what happened, what to do instead.
- **Did you build understanding that took real effort and is not plain in the
  code?** → new or updated `notes/topics/<slug>.md`, and add it to the index in
  `notes/topics/README.md`. Invariant shapes and *why* they have that shape are
  the prime example.
- **Did you choose a spec, invariant, abstraction, or trust boundary over a
  real alternative?** → new `notes/decisions/NNNN-slug.md` using the template in
  `notes/decisions/README.md`, and add it to that index. Record the rejected
  options and the cost that killed them.

## 5. Check your work

- Every claim cites a path, and line numbers where useful
  (`new/proof/go_etcd_io/raft/v3_proof/readonly.v:295`).
- No "as we discussed", no "the file above", no relative dates.
- Any new file is linked from the relevant index (`topics/README.md`,
  `decisions/README.md`).
- Read your `STATUS.md` back as if you had never seen this session. Could you
  resume from it alone? If not, fix it.

## 6. Commit

Commit the `notes/` changes along with the proof work, not separately — the
notes describe that commit's state. Mention notes in the commit message body.

## When the session did nothing worth recording

Exploration that changed nothing, a typo fix, a question answered — then say so
in one line and stop. Do not manufacture a journal entry. But if you changed
`.v` files, that is almost never the case.
