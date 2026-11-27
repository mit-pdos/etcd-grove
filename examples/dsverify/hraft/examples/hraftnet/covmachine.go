//go:build covmachine

package hraftnet

import "time"

// WarmOrch is Orch with the admin running alone for ms first and ops operations per client: the
// coverage runs' orchestrator (covmachine; examples/dsverify/hraftrobust). Not in the kit's build
// (tag covmachine): in the theorem, any schedule and any number Orch draws are allowed, so neither
// adds anything to it.
func WarmOrch(ms uint64, ops uint64) {
	configure(chooseN0())
	Register()
	go admin()
	time.Sleep(time.Duration(ms) * time.Millisecond)
	remoteCheck(ops)
}
