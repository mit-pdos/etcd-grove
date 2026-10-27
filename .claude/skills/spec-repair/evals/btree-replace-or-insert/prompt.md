---
tags: [spec-repair]
max_turns: 80
timeout_seconds: 3600
allowed_tools: [Read, Glob, Grep, Skill, Bash, Agent]
---

/spec-repair --review-only the B-tree's `BTree.ReplaceOrInsert` spec (Spec/k8s_io/utils/third_party/forked/golang/btree/BTree__ReplaceOrInsert.lean), the k8s fork of google/btree that etcd's cache uses. Is it the right contract for its clients?
