# Proof challenge

You are proving one Go function correct in Lean 4 with Perennial (a separation-logic framework
for Go, built on Iris), as part of a verification of google/btree.

**Your directory** (work only here; it is a private copy): `RUN_DIR`

**Your task**: in `EtcdGrove/Btree/Proof/CHALLENGE.lean`, replace the `sorry` with a proof of the
theorem. Do not change the theorem statement. You may add helper lemmas to that file (before the
theorem), and imports of modules that exist in this directory (`EtcdGrove/Btree/...` and
Perennial). Done means: the file compiles with no errors and no `sorry`.

**Rules (important; runs are audited)**: Use only files inside your directory. Do **not** use
git, do not read any other directory or copy of this repository, do not search the filesystem for
other versions of these files, and do not use the network. Other proofs in your directory
(`EtcdGrove/Btree/Proof/*.lean`) are fine to read and learn from.

**What is where**
- The spec you prove: `EtcdGrove/Btree/Spec/CHALLENGE.lean`; specs of callees: `Spec/*.lean`.
- Definitions: `EtcdGrove/Btree/{Defs,Model,Tree,Item}.lean`; lemmas: `ListLemmas.lean`,
  `NodeLemmas.lean`, `Lemmas/*.lean`; other proofs: `Proof/*.lean`.
- The Go code: `go/btree_generic.go`; its translation: `GoogleBtree/Code/github_com/google/btree.lean`.
- Perennial: `perennial/docs/PERENNIAL_PROOF_TUTORIAL.md`, `PERENNIAL_PROOF_REFERENCE.md`,
  `IRIS_PROOF_MODE.md`; sources in `perennial/Perennial/` (e.g. slice specs in
  `perennial/Perennial/Golang/Theory/Slice*.lean`, `Golang/Theory/Auto.lean` for `wp_auto`,
  `wp_apply`).

TOOLS_SECTION

**Finish** when the file compiles without errors or `sorry`, or if you are convinced it cannot be
done (e.g. the spec is false) — then explain why. Your final message: done / not done, and 2–5
sentences on what was hard.
