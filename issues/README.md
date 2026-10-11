# Issues found while verifying

One file per issue found in the verified Go code (raft, etcd, their dependencies) or its
documentation: a bug (a reachable panic or wrong result), a precondition the code needs
but its API does not state, or documentation the code contradicts. Not for bugs in this
repository's own specs and proofs (those go in `notes/`).

Name a file `<project>-<short-slug>.md` and give it:

- **Status**: open / reported (link) / fixed upstream (commit) / not a bug (why).
- **Where**: the Go code (file:line at the pinned revision in `etc/goose.py`) and the
  documentation involved.
- **What happens**: the behavior, with a reproduction (a Go test, inline or by path) when
  one exists.
- **Expected**: what the documentation or API promises instead.
- **How the proof handles it**: the premise, spec or scope choice that keeps it out of the
  verified results (file:line).
- **Possible fixes**.
- **Found**: date and by what (which proof or check).
