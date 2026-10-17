#!/bin/bash
# elaborate one file (imports must be built), printing its messages
cd /shared/etcd-grove-pr/raft-155
LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true lake env lean "$1" 2>&1 | grep -v "linter\|^Hint\|\[apply\]\|^Note" | head -${2:-150}
