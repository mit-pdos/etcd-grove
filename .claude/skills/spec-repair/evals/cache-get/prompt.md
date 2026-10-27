---
tags: [spec-repair]
max_turns: 80
timeout_seconds: 3600
allowed_tools: [Read, Glob, Grep, Skill, Bash, Agent]
---

/spec-repair --review-only etcd's watch cache `Cache.Get` spec (Spec/go_etcd_io/etcd/cache/v3/Cache__Get.lean). It sits between the B-tree and the client; is it a good contract at that boundary?
