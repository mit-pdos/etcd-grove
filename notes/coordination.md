# Coordinating on GitHub: the convention and `etc/gh-inbox.py`

Every session working on mit-pdos/etcd-grove, perennial and dsverify-lab posts as one of a few shared
GitHub accounts (`upamanyus-agent`, `zeldovich-agent`, `kaashoek`), so the account doesn't say which
session wrote a post. Until 2026-11-23 sessions told each other apart by free-text signatures, and each
session's own watcher filtered posts in its own way. Messages got lost:
- a watcher dropped every post addressed to "coordinator-E", taking them for its own;
- an approval was missed for an hour;
- a collaborator's Perennial PR waited ten hours without anyone seeing it.

This note is the convention all sessions follow. `etc/gh-inbox.py` reads it. Proposed on etcd-grove#8; it
takes effect once the three coordinators (`coordinator-E`, `zeldovich-coordinator`, `etcd-grove-03`) agree there.

## Handles: `etc/sessions.txt`

Each session that posts has a **handle**, e.g. `coordinator-E`, `dsverify-net`, `zeldovich-coordinator`,
`zeldovich-proving-2`, `etcd-grove-03` or `dsverify-lab`. Each person also has one: `upamanyus`,
`zeldovich`, `kaashoek`. The registry `etc/sessions.txt` has one row per handle, with:
- its owner, machine and GitHub account;
- its claims: what it does, and what the tool keys on (`relay`, `queue`, `lands:<repo>`, `reviews`);
- its old signatures and prose names, for posts written before the convention.

A session adds its row when it starts and removes it when it ends. The file is in the repository, so every
machine has it.

## A post

```
to: dsverify-lab, upamanyus (@kaashoek @upamanyus)

…the message…
ask: approve `gods-verified` at `74c9904d8c`?

from: coordinator-E
```

- **The first line** is `to:` followed by the handles the post is for, or `all`. `to: upamanyus` asks
  the person himself, for a real decision only. The `(@accounts)` part is optional: it makes GitHub notify
  those accounts, and the tool ignores it.
- **The last line** is `from: <handle>`. It's the only thing that makes a post a session's own. A mention
  of a handle never does: other sessions write "coordinator-E" to address it.
- **Action lines** start a line, outside code blocks and quotes:
  - `ask:`, `decision:`, `ack:`, `re:`, `done:`, `declined:` and `superseded-by:`. They're described
    below.
- **Queue lines are unchanged.** `land-queue: <branch> <sha>` and `vm-build: <branch> <sha> <command…>`
  keep their exact syntax: each is its own line, and the branch has no spaces. The queue's parser reads
  them, and so does the tool. Nothing about them changes.

`gh-inbox.py post --me H --to H… --issue N [--ask [TEXT]] FILE` adds the `to:` and `from:` lines and checks
the handles. It writes the result to `FILE.post` and prints the command that posts it:
`gh api repos/mit-pdos/<repo>/issues/N/comments -F body=@FILE.post`. The tool never posts, edits or closes
anything on GitHub itself. That was zeldovich's request, so a bug in it can't speak for a session.

## Items: what is open, and who closes it

An **item** is something someone has to act on. It is open, acked (someone has taken it) or closed.

Every session computes the state the same way, from the GitHub threads and the open PRs alone, so all
sessions and machines agree on it. There is no shared state anywhere else: `~/.cache/gh-inbox/<handle>/`
is only a cache.

| item (id) | opened by | acked by | closed by |
|---|---|---|---|
| ask (the comment id) | an `ask:` line in a post with `to:` | `ack: <id>`, or a `re: <id>` reply from an addressee | `re: <id> done: …` or `declined: …`, from an addressee; `superseded-by: <new id>`; the asker withdrawing it with `done:`/`declined:` |
| decision (the comment id) | a `decision:` line: a decision posted for the addressees to act on | the same | the same |
| land request (`queue:<branch>`) | a `land-queue:` line, addressed to the sessions that claim `queue` | the queue's "Enqueued `<branch>` at `<sha>`" (or re-enqueued) | the queue's "`<branch>` landed: `lean` is `<sha>`". A failure ("did not land", "failed", "conflict with current `lean`", "Held") sends the item back to the asker, who either re-sends the `land-queue:` line or closes the item. |
| VM build (`vm-build:<branch>@<sha>`) | a `vm-build:` line, addressed to the `queue` sessions | the VM's "running …" | the VM's "… finished" |
| PR to land (`land:<repo>#<n>`) | a non-draft PR by an account of another owner, in a repository someone claims with `lands:<repo>`, e.g. Perennial for `coordinator-E` | `ack: land:<repo>#<n>` | the PR merged or closed; or `done:`/`declined:` from the lander |
| review (`review:<repo>#<n>:<login>`) | a review request on GitHub | `ack:` | the request gone: the review submitted, or the request removed |

- **Rules for action lines:**
  - `ack:`, `done:` and `declined:` take the item ids after them. Without ids, they act on the ids of the
    post's `re:` lines.
  - A `re: <id>` with no verb is a reply, and counts as an ack. So an answer that closes an item must say
    `done:`; a sign-off is `re: <id> done: approved <branch> <sha>`.
  - `superseded-by:` with no id, in a post that asks again, means "superseded by this post's ask".
  - An id can be a comment id, an `issuecomment-…` link, a PR link or one of the ids in the table.
- **Who may act on an item:**
  - an addressee;
  - the asker, which withdraws it;
  - a `relay` session, for an item addressed to its owner.

  Anyone else's `done:` is ignored, and the item's history says so.

`gh-inbox.py open --for H` lists the open and acked items addressed to `H`, oldest first, with their
owner (who acked them) and their age. `open --by H` lists what `H` asked and is waiting for.
`digest --for upamanyus` (or `zeldovich`, `kaashoek`) lists what is waiting on that person: his
decisions, asks, reviews, PRs to land and land requests. `show ID` prints an item's history.

## Watching

`gh-inbox.py watch --me H` polls the three repositories and prints one line per event:
- posts to `H` or to `all` (and, for a `relay` session, to its owner);
- items for `H` that open, change hands or close;
- reminders of asks to `H` still open after `--remind` (default 6h);
- PRs waiting on `H` that are updated;
- reviews of `H`'s own PRs;
- changes to what `H` asked: an ack, an answer, a land request enqueued, failed or landed.

The polls cover issue comments, new and edited issues and PRs, open PRs and their requested reviewers.

**Options:**
- `--once` polls once.
- `--until-event` polls until it prints something, then exits. This suits sessions that wake on a
  notification.
- `--backlog 2h` also prints the last two hours on a first run.

**State across restarts.** The cursor (the newest `updated_at` seen) and what has been printed are kept in
`~/.cache/gh-inbox/H/`, so a restart resumes where the last run stopped. dsverify-net lost a decision this
way before.

**Rate limits.** Every request is conditional: an unchanged page costs a 304. Requests use
`since=<cursor>`, and back off on rate limits and server errors. The token is read from `GH_TOKEN` and is
never written or printed.

**Posts without the convention lines** (older posts, and anyone who forgets them):
- A post's author comes from its old signature in the registry, read only at the end of the post and never
  from a quote. Otherwise it's the person whose account posted it, or else `@<account>`.
- Such a post is for `H` if it names `H` or one of `H`'s prose names as a word, or `@`-mentions `H`'s account.

`scan --since DATE` (always a dry run) proposes the old posts that look like open asks: a question or a
request, addressed to a session, that no later post in the thread from an addressee answers. A proposal
becomes an item only when someone posts its ask with the convention. The tool never decides on its own that
an old post was an ask.

**The queue's result posts** (posted by `queue` sessions) are read from their first paragraph:
- the branch in backquotes or bare at the start;
- "Enqueued", "landed: `lean` is", "did not land", "failed", "conflict", "Held", "running" or "finished";
- a sentence saying "are re-queued: `a`, `b`, …".

Prose variants of these are not recognised. One result line per branch, in the forms above, keeps the
items right.

## Starting

1. Add your row to `etc/sessions.txt`.
2. Run `etc/gh-inbox.py watch --me <handle>` as your background monitor, and `open --for <handle>` at each
   wake-up.
3. Post with the `to:`/`from:` lines, by hand or through `post`.
4. Once, run `scan --since <date>`, and re-post any old ask still open with the convention.
5. Run `open --by <handle>` and close stale items with `done: <id>` (for example, land requests whose result
   post the tool couldn't read).

Tests: `python3 -m unittest discover -s etc/gh-inbox-test`. They use recorded JSON, with no network.
