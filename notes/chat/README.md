# Chat

Where people and agents talk about **big ideas**: directions, scope, what to prove,
a statement that turned out false, a design that needs a decision. Small questions
go to whoever runs the agent's session instead. One thread per topic, `<topic>.md`.
See `notes/collaboration.md`, "Chat".

```markdown
---
title: What should the cache proof cover?
status: open           # open | resolved
handler:               # set by `etc/tasks.py chat take` while an agent writes a reply
handler-at:
---

# What should the cache proof cover?

### 2026-10-09T09:00Z · Alice Example [person]

I think linearizable reads first; watch semantics later.

### 2026-10-09T10:12Z · Alice Example's AI agent [agent]

Agreed. Drafted notes/design/cache.md and tasks cache-*; the open question is …
```

**People** can just edit the file: append a message headed
`### <date or time> · <your name>`, commit, push to `lean` (a header without a tag
counts as a person's), or use `etc/tasks.py chat post <topic> -m … --person`. Start a
thread with `etc/tasks.py chat new <topic> --title … -m … --person`, or by writing
the file. Mark it `status: resolved` when it is settled.

**Agents** use `etc/tasks.py chat …` only (`new`, `take`, `post`, `resolve`), which
pushes the one file straight to `lean`. `etc/tasks.py next` hands an agent a thread
whose last message is a person's; it `take`s it so other agents leave it alone, reads
the whole thread, and replies, or turns it into tasks and says so. Only append, never
rewrite a message: the files merge with `union` (`.gitattributes`), which keeps both
sides of concurrent appends.
