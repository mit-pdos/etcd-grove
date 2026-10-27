---
tags: [spec-repair]
max_turns: 80
timeout_seconds: 3600
allowed_tools: [Read, Glob, Grep, Skill, Bash, Agent]
---

/spec-repair --review-only raft's `node.Propose` spec (Spec/go_etcd_io/raft/v3/node__Propose.lean). How good is this contract for raft's clients?
