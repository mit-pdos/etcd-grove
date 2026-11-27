// hashicorp/raft (notes/dsv-hraft.md): dsverify-lab's verification fork of hashicorp/raft v1.8.0
// (examples/hraft/fork/raft at lab c39f136, fork commit 02f88d5 on v1.8.0 0f543c0), without the
// lab's in-process harness. Translated into the part Dsverify/ (etc/goose.py, project dsv-hraft).
module github.com/hashicorp/raft

go 1.25.0

retract v1.1.3 // Deleted original tag; module checksum may not be accurate.

require github.com/goose-lang/primitive v0.2.2-0.20260212023729-cb7f52217e65
