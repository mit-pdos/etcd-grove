package bank

import (
	"os"
	"os/exec"
	"sync/atomic"
	"syscall"
	"testing"
	"time"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lib/lintest"
	bolt "go.etcd.io/bbolt"
)

// The helper process of TestBootKilled: boots again and again until killed.
func TestMain(m *testing.M) {
	if os.Getenv("BBOLTTEST_HELPER") == "bootloop" {
		for {
			Boot(os.Getenv("BBOLTTEST_DIR"))
		}
	}
	os.Exit(m.Run())
}

// readBank reads the bank and the witness's acknowledgements of dir.
func readBank(t *testing.T, dir string) (State, []uint64) {
	t.Helper()
	w, ok := openWitness(dir + "/witness")
	if !ok {
		t.Fatal("open witness")
	}
	defer w.close()
	acked, ok := w.acked()
	if !ok {
		t.Fatal("read witness")
	}
	db, err := bolt.Open(dir+"/db", 0o600, nil)
	if err != nil {
		t.Fatal(err)
	}
	defer db.Close()
	var s State
	var exists bool
	if err := db.View(func(tx *bolt.Tx) error {
		s, exists = readState(tx)
		return nil
	}); err != nil || !exists {
		t.Fatalf("read bank: %v, exists %v", err, exists)
	}
	return s, acked
}

// Booted again and again without crashes, Boot never panics, and every transfer of every boot
// commits and is acknowledged.
func TestBoot(t *testing.T) {
	dir := t.TempDir()
	const boots = 5
	for i := 0; i < boots; i++ {
		Boot(dir)
	}
	s, acked := readBank(t, dir)
	// each client's ops: two transfers of every three
	perBoot := uint64(nOps - nOps/3)
	for c := 0; c < nClients; c++ {
		if s.Seq[c] != boots*perBoot || acked[c] != s.Seq[c] {
			t.Fatalf("client %d: seq %d, acked %d, want %d", c, s.Seq[c], acked[c], boots*perBoot)
		}
	}
}

// Boot in a process that is killed (SIGKILL) at arbitrary points and restarted. A killed process
// is not a crash of the node (the page cache survives), so this checks that no boot's assertion
// fires when a boot is cut short, not the crash relation of the model.
func TestBootKilled(t *testing.T) {
	if testing.Short() {
		t.Skip("slow")
	}
	dir := t.TempDir()
	for i := 0; i < 10; i++ {
		cmd := exec.Command(os.Args[0], "-test.run=^$")
		cmd.Env = append(os.Environ(), "BBOLTTEST_HELPER=bootloop", "BBOLTTEST_DIR="+dir)
		if err := cmd.Start(); err != nil {
			t.Fatal(err)
		}
		time.Sleep(time.Duration(50+37*i) * time.Millisecond)
		_ = cmd.Process.Kill()
		err := cmd.Wait()
		ee, ok := err.(*exec.ExitError)
		if !ok {
			t.Fatalf("boot loop %d: %v", i, err)
		}
		if ws := ee.Sys().(syscall.WaitStatus); !ws.Signaled() || ws.Signal() != syscall.SIGKILL {
			t.Fatalf("boot loop %d ended by itself (a panic?): %v", i, err)
		}
	}
	Boot(dir)
	s, acked := readBank(t, dir)
	for c := 0; c < nClients; c++ {
		if s.Seq[c] < acked[c] || acked[c] == 0 {
			t.Fatalf("client %d: seq %d, acked %d", c, s.Seq[c], acked[c])
		}
	}
}

// Recovery finds a lost acknowledged transfer: a witness that acknowledges more than the
// database holds.
func TestRecoveryDetectsLoss(t *testing.T) {
	dir := t.TempDir()
	Boot(dir)
	s, _ := readBank(t, dir)
	w, _ := openWitness(dir + "/witness")
	if !w.ack(1, s.Seq[1]+1) {
		t.Fatal("ack")
	}
	w.close()
	defer func() {
		if recover() == nil {
			t.Fatal("recovery accepted a lost transfer")
		}
	}()
	Boot(dir)
}

// Recovery finds a torn transfer: balances that do not add up.
func TestRecoveryDetectsTear(t *testing.T) {
	dir := t.TempDir()
	Boot(dir)
	db, err := bolt.Open(dir+"/db", 0o600, nil)
	if err != nil {
		t.Fatal(err)
	}
	if err := db.Update(func(tx *bolt.Tx) error {
		return tx.Bucket(bucketName()).Put(accountKey(0), encode(1))
	}); err != nil {
		t.Fatal(err)
	}
	db.Close()
	defer func() {
		if recover() == nil {
			t.Fatal("recovery accepted a torn transfer")
		}
	}()
	Boot(dir)
}

// A slot whose flag is clear is ignored: its number may be torn.
func TestWitnessFlag(t *testing.T) {
	path := t.TempDir() + "/witness"
	w, ok := openWitness(path)
	if !ok || !w.ack(2, 7) || !w.ack(2, 8) {
		t.Fatal("ack")
	}
	// a torn write in slot 1 (sequence number 9's): flag cleared, number garbage
	if !w.writeSync([]byte{0}, (2*2+1)*slotSize+8) || !w.writeSync(encode(1<<60), (2*2+1)*slotSize) {
		t.Fatal("write")
	}
	acked, ok := w.acked()
	if !ok || acked[2] != 8 || acked[0] != 0 {
		t.Fatalf("acked %v", acked)
	}
	w.close()
	// reopened: initialized, so not reset
	w, ok = openWitness(path)
	if !ok {
		t.Fatal("reopen")
	}
	defer w.close()
	if acked, _ := w.acked(); acked[2] != 8 {
		t.Fatalf("after reopen: acked %v", acked)
	}
}

// porcupine rejects a bank whose transfer is not one transaction (it reads in one and writes in
// another, losing updates): the check has teeth.
func TestCheckRejectsNonSerializable(t *testing.T) {
	db, err := bolt.Open(t.TempDir()+"/db", 0o600, &bolt.Options{NoSync: true})
	if err != nil {
		t.Fatal(err)
	}
	defer db.Close()
	k := &bank{db: db}
	if err := db.Update(func(tx *bolt.Tx) error {
		b, err := tx.CreateBucket(bucketName())
		if err != nil {
			return err
		}
		for i := uint64(0); i < nAccounts; i++ {
			if err := b.Put(accountKey(i), encode(initBalance)); err != nil {
				return err
			}
		}
		return nil
	}); err != nil {
		t.Fatal(err)
	}
	var init State
	for i := range init.Bal {
		init.Bal[i] = initBalance
	}
	var calls atomic.Int64
	racy := func(input any) any {
		op := input.(Op)
		if op.Read {
			return k.apply(input)
		}
		var s State
		_ = db.View(func(tx *bolt.Tx) error { s, _ = readState(tx); return nil })
		if calls.Add(1)%2 == 0 {
			time.Sleep(2 * time.Millisecond)
		}
		res, next := step(s, op)
		_ = db.Update(func(tx *bolt.Tx) error {
			b := tx.Bucket(bucketName())
			b.Put(seqKey(op.Client), encode(next.Seq[op.Client]))
			b.Put(accountKey(op.From), encode(next.Bal[op.From]))
			return b.Put(accountKey(op.To), encode(next.Bal[op.To]))
		})
		return res
	}
	r := lintest.Run(Model(init), racy, generator(), lintest.CounterClock(), nClients, nOps, 10*time.Second)
	if r != porcupine.Illegal {
		t.Fatalf("got %v", r)
	}
}
