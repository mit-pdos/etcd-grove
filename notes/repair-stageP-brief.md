# Stage P of the client repair: the common brief for every track helper

You are one of up to four helpers proving, in parallel and IN THE SAME WORKTREE, the `sorry`s Stage F
left in etcd's server and examples/kv, each exactly once, against frozen statements.

Worktree: /home/ubuntu/etcd-grove/.claude/worktrees/raft-spec-review (branch `repair`). Do not cd
elsewhere, do not create worktrees, do not switch branches. Scratch: /home/ubuntu/.claude-E/jobs/c8379647/tmp
(make your own subdirectory there, named after your track).

## Read first (only what you need)

- CLAUDE.md (proof writing, records, `word`, lean-check, modules).
- notes/raft-unified-plan.md, the sections "Repair: Stage F statements", "Repair: Stage F sorries"
  (your track's list), "Repair: Stage F revision, snapshots allowed", "Repair: snapshot sorries".
- notes/repair-design.md §4 (invariant design) for your part, and its "User decisions" section.
- Raft's API as clients see it: interface/Proof/go_etcd_io/raft/v3/*.txt, interface/Spec/go_etcd_io/raft/v3/*.txt.
- Each broken proof's old body is in a `/- REPAIR-OLD … -/` comment beside it: your starting point.
  Delete the REPAIR-OLD comment once the proof replacing it is done.
- examples/kvreconf's proofs (Proof/github_com/mit_pdos/etcd_grove/examples/kvreconf/) are proved over
  the same unified raft API: templates for the storage wrapper, the run loop, allocation, Ready/Advance.

## Rules

1. **Your files only.** You edit only the files your track lists, plus new lemma modules you create
   (name them so their owner is clear, e.g. `<Dir>/<Track>Lemmas*.lean` or after the function), plus
   new files in `issues/`. Do not edit notes/ (the coordinator keeps the plan and STATUS), Link.lean,
   Results.lean, interface/, etc/.
2. **Statements are frozen.** Do not change the statement of any existing theorem/def/axiom, nor any
   definition (predicate, invariant), in any file, including your own, without the coordinator's
   answer. You may add new lemmas (in your files or new modules) and change proof bodies freely.
   Private helper lemmas used only inside your own file are yours.
   When a frozen statement or invariant turns out wrong or unprovable (false of the Go, a premise
   missing, an invariant too weak): STOP that proof, keep working on your other sorries if they do
   not depend on it, and when you cannot go further, END YOUR TURN with a report starting
   `QUESTION:` that states precisely: the declaration, why it is false/unprovable (a counterexample
   or the missing fact), and the minimal fix you propose (old text → new text, framed as its own
   predicate where possible so other proofs stay unchanged), and which other files it affects. The
   coordinator answers by resuming you (SendMessage). Do not wait/poll; just end the turn.
   Exception (minor, decide yourself and log in your report): a missing instance argument, a
   lemma's argument order, a typo-level fix that changes no meaning — still only in your own files.
3. **SNAPSHOT-SORRY.** The branches marked `-- SNAPSHOT-SORRY` stay `sorry` (the user approved
   them): where a whole proof is a stage-P `sorry` with such a marker, prove everything except that
   branch, closing exactly the marked branch with `sorry -- SNAPSHOT-SORRY: <what>`. Add no other
   `sorry`, no `axiom`, no new ghost state. If you think another path is snapshot-only, ask.
4. **Edit loop.** `etc/lean-check.py FILE` (`--goal LINE` for the state, `--fast` in the loop, a final
   check without `--fast`). Before relying on a module you did not build (an import changed), run
   `lake build <Module.Name>` of that module only. Never run a full `lake build`, `etc/tcb-report.py`,
   or gen-interface: the coordinator does. Lake serializes concurrent builds in this worktree (it may
   print that it is waiting for another build: let it wait). Never `sleep`-poll; never kill processes
   by name (other sessions share the machine); kill only your own by PID.
   Keep proofs in modules small enough to re-check quickly: when a file's proof grows long, move
   lemmas into a new small module (`public import`ed by the file that needs it; the new module starts
   with `module`, `public import`s, `@[expose] public section`, as CLAUDE.md "Modules" says). Use
   `--split` on very long proofs.
   **A file other modules import must compile on disk at all times** (other helpers' checks rebuild
   it with Lake; a broken copy deletes its .olean and blocks everyone importing it). Draft a proof
   in an uncommitted scratch copy (`<File>Draft.lean` next to it, imported by nothing, deleted
   before you finish) or in a new module nothing imports until it checks; splice the proof in only
   once it checks, then re-check the real file and `lake build` its module. Only leaf files nobody
   imports may be edited in place while broken.
5. **Commit per proved lemma or group**, only your files, with explicit paths:
   `git add <files> && git commit -m "server Stage P (<track>): <what>" -- <files>`
   (end the message with `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`); then
   `git push origin repair` (if it is rejected because another helper pushed, `git pull --rebase
   origin repair` is NOT needed: all helpers commit to the same local branch, so just retry the push;
   if the git index is locked, retry after a few seconds). Never `git stash`, never `git add -A`,
   never commit another helper's files, never reset/checkout files you do not own.
   A commit must not leave your file broken (it must check with lean-check; a remaining stage-P sorry
   is fine).
6. **Bugs in the Go code** (a reachable panic, wrong result, undocumented precondition): a file in
   `issues/` per issues/README.md, and say so in your report.
7. **Report** (your final message): each sorry of your track: proved / still sorry (why) / the
   SNAPSHOT-SORRY kept; every new lemma module; every minor deviation; any QUESTION; commits pushed;
   anything another track should know (a lemma you proved that they can use, a frozen statement you
   suspect is wrong elsewhere).
