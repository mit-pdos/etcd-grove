# Fork commits not yet pushed

A change to Go code goes to the fork (CLAUDE.md, "The Goose translations"); a commit made for
this repository that cannot be pushed yet is kept here, as `git format-patch` output, so that the
local fork branch can be recreated and the translation regenerated. Each file says which project's
fork it belongs to and what the translation in this repository was generated from. Remove a patch
once its commit is pushed and `etc/goose.py`'s pin points at it.

None at present. (Until 2026-11-15, `raft-trace-tags.patch`: raft's trace hooks under the `goose`
build tag. Replaced by goose's `-tags`: `etc/goose.py`, `RAFT_TAGS`; raft's source is unchanged.)
