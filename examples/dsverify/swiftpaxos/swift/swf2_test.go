package swift

import (
	"testing"
	"time"
)

// SW-F2: the reply goroutine hands out the history slots modulo the
// history's size; a descriptor goroutine writes its slot's fields when it
// takes the slot. With more replies than slots (unboundedly many commands;
// each recovery re-executes and re-replies the whole history), a slot is
// handed out again while (or after) its previous holder writes it, with
// nothing ordering the two writes: a data race (Go's memory model).
//
// The history has two slots (the reply goroutine counts modulo the
// history's length, HISTORY_SIZE in New: the test's small history stands
// for HISTORY_SIZE). Three descriptors with goroutines, all created first,
// are replied to: slots 0, 1, 0. The first and the third write slot 0.
// Skipped without -race (a data race; go test -race -run TestIssueSWF2).
func TestIssueSWF2_HistorySlotReuse(t *testing.T) {
	if !raceOn {
		t.Skip("a data race: run with -race")
	}
	old := MaxDescRoutines
	MaxDescRoutines = 100
	defer func() { MaxDescRoutines = old }()

	r := newTestReplica(t, 3, 0, 0, false)
	r.history = make([]commandStaticDesc, 2)
	r.repchan = NewReplyChan(r)

	descs := []*commandDesc{}
	for i := int32(0); i < 3; i++ {
		descs = append(descs, r.getCmdDesc(cid(1, i), nil, nil))
	}
	for i, desc := range descs {
		desc.propose = put(cid(1, int32(i)), 6, "v")
		r.repchan.reply(desc, cid(1, int32(i)), nil)
	}
	for start := time.Now(); r.cmdDescs.Count() != 0; {
		if time.Since(start) > 10*time.Second {
			t.Fatal("the descriptors did not take their history slots")
		}
		time.Sleep(time.Millisecond)
	}
	r.repchan.stop()
}
