---
tags: [spec-repair]
max_turns: 80
timeout_seconds: 3600
allowed_tools: [Read, Glob, Grep, Skill, Bash, Agent]
---

/spec-repair --review-only etcd client's `kv.Put` spec (Spec/go_etcd_io/etcd/client/v3/kv__Put.lean), the top-level KV API applications use. Is it the contract an application needs?
