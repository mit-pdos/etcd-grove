//go:build covmachine

package hraftnet

import "time"

// WarmOrch is Orch with the admin running alone for ms first: the coverage runs' orchestrator
// (covmachine; examples/dsverify/hraftrobust). Not in the kit's build (tag covmachine): in the
// theorem, any schedule is allowed, so the wait adds nothing to it.
func WarmOrch(ms uint64) {
	configure(chooseN0())
	Register()
	go admin()
	time.Sleep(time.Duration(ms) * time.Millisecond)
	remoteCheck()
}
