# Fork commits not yet pushed

A change to Go code goes to the fork (CLAUDE.md, "The Goose translations"); a commit made for
this repository that cannot be pushed yet is kept here, as `git format-patch` output, so that the
local fork branch can be recreated and the translation regenerated. Each file says which project's
fork it belongs to and what the translation in this repository was generated from. Remove a patch
once its commit is pushed and `etc/goose.py`'s pin points at it.

- `raft-trace-tags.patch` (project `raft`, on the pinned `565c2bd`): the trace hooks under the
  `goose` build tag, so that Goose translates raft's `with_tla` build. Branch
  `raft37-goose-lean-a2-trace`, commit `e8f9566`, not pushed to `upamanyus/etcd` (2026-11-08).
  Branch `trace-check`'s raft translation is generated from it:

      git clone .lake/goose/raft .lake/raft-trace   # after any etc/goose.py run has cloned the pin
      cd .lake/raft-trace && git checkout 565c2bd && git switch -c raft37-goose-lean-a2-trace
      git am ../../etc/fork-patches/raft-trace-tags.patch && cd ../..
      GOARCH=amd64 CGO_ENABLED=1 CC=x86_64-linux-gnu-gcc \
        etc/goose.py --project raft --src raft=.lake/raft-trace

  (`GOARCH`... only on a non-amd64 host: the checked-in translations are amd64's.) Until the
  commit is pushed and the pin moved, `etc/goose.py --check` fails for raft on that branch, and
  the branch cannot land.
