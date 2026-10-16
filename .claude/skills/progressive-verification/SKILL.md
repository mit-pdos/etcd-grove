---
name: progressive-verification
description: Formally specify and verify a function.
---

Your goal is to apply progressive verification to one of the functions in
the etcd implementation.  Read the paper about progressive verification
at paper.pdf.  Clone the etcd source code from github.com/etcd-io/etcd
and github.com/etcd-io/raft (as appropriate), and use Goose and Perennial
(github.com/mit-pdos/perennial, branch lean) to start verifying the
function in a progressive style.  You will need to state postulates
for any callee functions that don't already have proven specs (Perennial
proves some Go standard library functions already), you will need to state
invariants for shared state, and you will need to understand the function
you're proving, and write a spec for that function that captures its
intended behavior.  Once you write the postulates, invariants, and spec,
then iterate on them with a fresh review subagent; its job will be to catch
potential soundness issues in your assumed postulates and invariants,
and audit whether your top-level proposed spec correctly captures the
intended behavior of the function.  Be sure to pay careful attention to
concurrency, in the postulates, invariants, and the function spec.
