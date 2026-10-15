# raft: `tracker.Config.Clone` drops `AutoLeave`, so `Status().Config.AutoLeave` is always false

**Status**: open (not reported upstream; not checked whether raft after `40f8be7` fixed it).

**Where** (etcd-io/raft at `40f8be730b18`, the revision `etc/goose.py` pins):

- `tracker/tracker.go:95-109`: `Config.Clone`, documented "Clone returns a copy of the
  Config that shares no memory with the original", builds
  `Config{Voters: ..., Learners: ..., LearnersNext: ...}`: `AutoLeave` is not copied, so the
  copy has `AutoLeave = false`.
- `status.go:74`: `getStatus` reports `s.Config = r.trk.Config.Clone()`.
- `confchange/confchange.go:337-347`: `Changer.checkAndCopy` copies with `Clone`.

**What happens**: in a joint configuration entered with auto-leave (`EnterJoint(true, ...)`,
a `ConfChangeV2` with `ConfChangeTransitionJointImplicit` or `Auto`), `Status().Config` and
anything else built with `Clone` reports `AutoLeave: false`, unlike the configuration it
copies. Inside `confchange` it is harmless: every `Changer` method either rejects a joint
configuration or overwrites `AutoLeave` (`EnterJoint` sets it, `LeaveJoint` clears it).
Reproduction (a test in package `confchange`):

```go
func TestCloneDropsAutoLeave(t *testing.T) {
	tr := tracker.MakeProgressTracker(10, 0)
	c := Changer{Tracker: tr, LastIndex: 1}
	cfg, prs, err := c.Simple(pb.ConfChangeSingle{Type: pb.ConfChangeAddNode, NodeId: 1})
	if err != nil {
		t.Fatal(err)
	}
	tr.Config, tr.Progress = cfg, prs
	c = Changer{Tracker: tr, LastIndex: 1}
	cfg, _, err = c.EnterJoint(true, pb.ConfChangeSingle{Type: pb.ConfChangeAddNode, NodeId: 3})
	if err != nil || !cfg.AutoLeave {
		t.Fatal(err)
	}
	if cfg.Clone().AutoLeave {
		t.Fatal("Clone kept AutoLeave")
	}
	// passes: Clone() has AutoLeave == false
}
```

**Expected**: a copy, `AutoLeave` included, as the documentation says (or documentation
saying `Clone` resets it).

**How the proof handles it**: `tracker.Config.Clone.spec` states the clone with
`autoLeave := false` (`Spec/go_etcd_io/raft/v3/tracker/Config__Clone.lean`), and the
`confchange` model clears it in `checkAndCopy` (`clearAutoLeave`, `InvConfchange.lean`).

**Possible fixes**: copy the field (`AutoLeave: c.AutoLeave` in `Clone`'s literal), or
document the reset.

**Found**: 2026-10-12, while generalizing the `confchange` specs (the spec of `Config.Clone`).
