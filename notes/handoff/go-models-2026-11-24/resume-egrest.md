# egrest resume notes

State (2026-11-24):
- Perennial B1: branch goose-model-overlay-rest-xtools 41b2523e4 (pushed), worktree pgmR-xtools (do not edit).
- etcd-grove shared worktree eg-gmr, branch go-models-rest/2026-11-24. Mine pushed: 6bfc699d3f (B2 gomodel),
  97e1b44ff3 (CI pin + go/token model file/toml), 9dac1834d6 (tcb-report Go models, model-tests; ALSO the
  deletions of TrustedCode/hash/crc32.lean and Net/TrustedCode/go/token.lean, so HEAD needs the next commit).
- Uncommitted (mine): Code/hash/crc32.{lean,toml}, GeneratedProof/hash/crc32.lean, models/hash/**, Net/Code/go/token.lean,
  Net/GeneratedProof/go/token.lean, Net/{Spec,Proof}/go/token/IsExported.lean, Proof/hash/crc32/{Init,InitLinked,
  archAvailableCastagnoli,archUpdateCastagnoli}.lean, Spec/hash/crc32/{Model,Update,arch*}.lean, Proof/internal/gomodel/
  {Base,Init,LocalChoose}.lean (LOCAL), etc/gen-init.py (PERENNIAL_HERE += internal.gomodel), etc/goose.py (J3 ->
  [model] files, needs_models_lab), Code/.../membership.{toml,lean}, models/go.etcd.io/**, membership InitLinked,
  36 Dsverify PkgTable.lean (gen-init, from go/token importing gomodel).
- Not mine (do not commit): Code/os.toml, models/os/**, Code/syscall*, Net/Code/net*, models/net/model.go etc.

Next:
1. VM build (log build1.log): Proof.hash.crc32.InitLinked Net.Proof.go.token.IsExported Proof.internal.gomodel.Init
   Spec.hash.crc32.Update; fix proofs; then importers (etc/importers.py) + Proof.internal.gomodel.LocalChoose.
2. Commit crc32 + token + J3; push; tell lead.
3. goose.py --check for all projects reaching membership/crc32/token (flock lock); gen-init --check.
4. Packet: tcb-report before/after (VM), #print axioms, model vs real Go side by side.
Commands: goose-howto.md; gen-init needs PERENNIAL_DIR=/home/ubuntu/.claude-E/jobs/b20ef685/tmp/gmr-egrest/perennial-pin.

## 2026-11-24 (respawn) state
Head 14aa39bd7f pushed: my modules all build on the VM; #print axioms clean; model-tests pass; goose --check
clean for crc32/token projects. Packet: gmr-egrest/packet.md. Blocked on egos: gen-init NET_MAIN += internal.filepathlite
and regen; Proof.syscall.*/Proof.os.Base fail -> rest of cone + tcb-report before/after pending.
Rebuild: vmlake build $(grep -v '^notes\.' gmr-egrest/leaves.txt | tr '\n' ' ')
