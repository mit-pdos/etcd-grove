# Examples

Cleanups the user picked as the kind this skill should find: each file gives what is there, why the
current proofs do not need it (the evidence, found the way a cleanup should find it), what goes and
what stays, and the checks. Read this index, then open only the examples whose kind matches what you are
looking at.

| Example | Kind | Shows |
|---|---|---|
| [resnapokraw.md](resnapokraw.md) | **an injected predicate nothing needs**: a library's ghost state takes a client's predicate as a parameter (HOCAP style: the library carries and promises a property it does not understand), while client-owned ghost state (a registry with a ghost or logically atomic update, each client's property in its own invariant) already does the job and every use of the parameter pins it to `True` (raft's `RaftNames.reSnapOkRaw`) | judge the proofs as they are: an injected predicate is unwanted, and one nothing needs is deleted; find that by classifying every use (trivial premise, pass-through, unused definition) and checking each client states its property on its own side; history explains a choice, it does not justify deleting; count the rebuild |

Keep it small: an example is readable in one sitting; when a newer example shows the same lesson
better, remove the older one from this index (git keeps it).
