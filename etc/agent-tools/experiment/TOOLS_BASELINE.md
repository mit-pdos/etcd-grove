**Tools**
- `./check FILE.lean` (run from your directory): compiles the whole file and prints Lean's
  messages (errors, warnings, and the unsolved goals in error messages). To see the proof state at
  some point, a common trick is to end the proof there (e.g. with `done`, or `trace_state` /
  `sorry`) and read the error/output.
