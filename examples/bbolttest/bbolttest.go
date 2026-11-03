// Package bbolttest is the top-level test of bbolt (the fork upamanyus/bbolt, branch goose-lean,
// which etc/goose.py's project bbolttest translates): a program over real bbolt whose panics never
// fire, however often the node crashes, if bbolt's transactions are durable and strictly
// serializable.
//
// The database is a bank: nAccounts balances and one sequence number per client, in one bucket.
// Boot runs once per boot of the node:
//
//  1. Recovery. It opens the database and a witness file and checks the state it finds:
//     - atomicity: the balances sum to the initial total (every transfer moves money, all or
//     nothing);
//     - durability: each client's sequence number in the database is at least the largest one the
//     witness file says was acknowledged, i.e. every transaction whose Update returned nil
//     before the crash is in the database.
//  2. Strict serializability. nClients clients run transactions concurrently through the lintest
//     driver: transfers (an Update that reads two balances, moves money if it can, and increments
//     the client's sequence number) and snapshot reads (a View of the whole bank). porcupine
//     checks the trace against the bank's sequential model, started from the recovered state.
//     Transactions are porcupine's operations, so a linearizable trace is a strictly serializable
//     execution of the transactions.
//
// After each transfer's Update returns nil, the client records its new sequence number in the
// witness file and makes it durable, so the next boot can check it.
//
// A failed system call (any error from bbolt or the file) is an environmental failure: the client
// stops, and Boot then returns without judging porcupine's answer (a failed commit may or may not
// have taken effect, so the trace has no outcome for it). Boot panics only on a violation.
package bbolttest

import (
	"os"
	"sync"
	"sync/atomic"
	"syscall"

	"github.com/anishathalye/porcupine"
	"github.com/mit-pdos/etcd-grove/examples/lintest"
	bolt "go.etcd.io/bbolt"
)

const (
	nAccounts   = 4
	initBalance = 100
	nClients    = 3
	// operations per client per boot
	nOps = 8
)

// State is the bank: the balances and each client's sequence number (the number of its transfers
// that committed, over all boots).
type State struct {
	Bal [nAccounts]uint64
	Seq [nClients]uint64
}

// Op is one transaction: a snapshot read (Read), or client Client's transfer of Amount from
// account From to account To.
type Op struct {
	Read   bool
	Client uint64
	From   uint64
	To     uint64
	Amount uint64
}

// Result is a transaction's outcome: a read's snapshot, or whether a transfer moved the money (it
// does when From's balance covers Amount). Failed: the transaction got an error.
type Result struct {
	Snap   State
	Moved  bool
	Failed bool
}

// step is a transaction's sequential specification: its result and the next state.
func step(s State, op Op) (Result, State) {
	if op.Read {
		return Result{Snap: s}, s
	}
	next := s
	next.Seq[op.Client] = s.Seq[op.Client] + 1
	moved := s.Bal[op.From] >= op.Amount
	if moved {
		next.Bal[op.From] = s.Bal[op.From] - op.Amount
		next.Bal[op.To] = next.Bal[op.To] + op.Amount
	}
	return Result{Moved: moved}, next
}

// Model is the bank's sequential specification for porcupine, from the state init.
func Model(init State) porcupine.Model {
	return porcupine.Model{
		Init: func() any { return init },
		Step: func(state, input, output any) (bool, any) {
			want, next := step(state.(State), input.(Op))
			return output.(Result) == want, next
		},
		Equal: func(a, b any) bool { return a.(State) == b.(State) },
	}
}

func bucketName() []byte { return []byte("bank") }

func accountKey(i uint64) []byte { return []byte{'a', byte(i)} }

func seqKey(c uint64) []byte { return []byte{'s', byte(c)} }

// encode is v's 8 bytes, little-endian.
func encode(v uint64) []byte {
	return []byte{byte(v), byte(v >> 8), byte(v >> 16), byte(v >> 24), byte(v >> 32),
		byte(v >> 40), byte(v >> 48), byte(v >> 56)}
}

// decode is the little-endian value of b's first 8 bytes; 0 unless b has 8 bytes (a missing key).
func decode(b []byte) uint64 {
	if len(b) != 8 {
		return 0
	}
	return uint64(b[0]) | uint64(b[1])<<8 | uint64(b[2])<<16 | uint64(b[3])<<24 |
		uint64(b[4])<<32 | uint64(b[5])<<40 | uint64(b[6])<<48 | uint64(b[7])<<56
}

// readState reads the bank in tx; ok is false if the bucket does not exist.
func readState(tx *bolt.Tx) (State, bool) {
	var s State
	b := tx.Bucket(bucketName())
	if b == nil {
		return s, false
	}
	for i := uint64(0); i < nAccounts; i++ {
		s.Bal[i] = decode(b.Get(accountKey(i)))
	}
	for c := uint64(0); c < nClients; c++ {
		s.Seq[c] = decode(b.Get(seqKey(c)))
	}
	return s, true
}

// A bank is the database and the witness, shared by the clients of one boot.
type bank struct {
	db      *bolt.DB
	witness *witness
	// set by the first client that gets an error
	failed atomic.Bool
}

// apply runs one transaction. After an error (this client's or another's) it runs nothing and
// returns a failed result.
func (k *bank) apply(input any) any {
	op := input.(Op)
	if k.failed.Load() {
		return Result{Failed: true}
	}
	if op.Read {
		var s State
		err := k.db.View(func(tx *bolt.Tx) error {
			s, _ = readState(tx)
			return nil
		})
		if err != nil {
			k.failed.Store(true)
			return Result{Failed: true}
		}
		return Result{Snap: s}
	}
	var moved bool
	var seq uint64
	err := k.db.Update(func(tx *bolt.Tx) error {
		b := tx.Bucket(bucketName())
		from := decode(b.Get(accountKey(op.From)))
		to := decode(b.Get(accountKey(op.To)))
		seq = decode(b.Get(seqKey(op.Client))) + 1
		if err := b.Put(seqKey(op.Client), encode(seq)); err != nil {
			return err
		}
		moved = from >= op.Amount
		if moved {
			if err := b.Put(accountKey(op.From), encode(from-op.Amount)); err != nil {
				return err
			}
			if err := b.Put(accountKey(op.To), encode(to+op.Amount)); err != nil {
				return err
			}
		}
		return nil
	})
	if err != nil {
		k.failed.Store(true)
		return Result{Failed: true}
	}
	// the transfer is acknowledged: the next boot must find it
	if !k.witness.ack(op.Client, seq) {
		k.failed.Store(true)
	}
	return Result{Moved: moved}
}

// generator returns lintest's input generator: client id's i-th operation (a per-client count,
// each client touching only its own) is a read when i%3 == 2, and otherwise a transfer between
// two adjacent accounts chosen by id and i, of an amount that sometimes exceeds the balance.
func generator() func(int) any {
	counts := make([]uint64, nClients)
	return func(id int) any {
		c := uint64(id)
		i := counts[c]
		counts[c] = i + 1
		if i%3 == 2 {
			return Op{Read: true}
		}
		from := (c + i) % nAccounts
		return Op{Client: c, From: from, To: (from + 1) % nAccounts, Amount: 30 + 40*((c+i)%4)}
	}
}

// recoverState checks the state the database holds against the witness's acknowledgements, and
// creates the bank if the database has none. ok is false on an environmental failure.
func recoverState(db *bolt.DB, w *witness) (State, bool) {
	acked, ok := w.acked()
	if !ok {
		return State{}, false
	}
	var s State
	var exists bool
	if err := db.View(func(tx *bolt.Tx) error {
		s, exists = readState(tx)
		return nil
	}); err != nil {
		return State{}, false
	}
	if !exists {
		for c := uint64(0); c < nClients; c++ {
			if acked[c] != 0 {
				panic("bbolttest: an acknowledged transfer is lost (the bank is gone)")
			}
		}
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
			return State{}, false
		}
		var init State
		for i := uint64(0); i < nAccounts; i++ {
			init.Bal[i] = initBalance
		}
		return init, true
	}
	total := uint64(0)
	for i := uint64(0); i < nAccounts; i++ {
		total = total + s.Bal[i]
	}
	if total != nAccounts*initBalance {
		panic("bbolttest: the balances do not add up (a transfer is torn)")
	}
	for c := uint64(0); c < nClients; c++ {
		if s.Seq[c] < acked[c] {
			panic("bbolttest: an acknowledged transfer is lost")
		}
	}
	return s, true
}

// Boot is one boot of the node: recovery's checks, then nClients concurrent clients of nOps
// transactions each, checked by porcupine. It panics only on a violation, and returns on any
// environmental failure.
func Boot(dir string) {
	w, ok := openWitness(dir + "/witness")
	if !ok {
		return
	}
	db, err := bolt.Open(dir+"/db", 0o600, nil)
	if err != nil {
		w.close()
		return
	}
	init, ok := recoverState(db, w)
	if !ok {
		db.Close()
		w.close()
		return
	}
	k := &bank{db: db, witness: w}
	r := lintest.Run(Model(init), k.apply, generator(), lintest.CounterClock(), nClients, nOps, 0)
	if !k.failed.Load() && r != porcupine.Ok {
		panic("bbolttest: the transactions are not strictly serializable")
	}
	db.Close()
	w.close()
}

// The witness file: per client, two slots of an 8-byte acknowledged sequence number guarded by a
// flag byte, then (at offset witnessSize) a flag that says the slots were initialized to zero
// and made durable. A slot's flag is set only after its number is durable, and cleared (durably)
// before the number is overwritten, so a set flag always guards an acknowledged number: a crash
// can tear a number being written, but its flag is then clear. The slots alternate (sequence
// number s goes to slot s%2), so the other slot keeps an earlier acknowledgement meanwhile. As in
// examples/crashlog, the initialization flag comes after the data: until the zeroed slots are
// durable, a crash may leave arbitrary bytes in the extended file, but no initialization flag.
const (
	slotSize    = 9
	witnessSize = nClients * 2 * slotSize
)

type witness struct {
	mu sync.Mutex
	f  *os.File
}

// openWitness opens the witness file, initializing it if it has no initialization flag (it was
// never initialized, so nothing was ever acknowledged).
func openWitness(path string) (*witness, bool) {
	f, err := os.OpenFile(path, os.O_RDWR|os.O_CREATE, 0o600)
	if err != nil {
		return nil, false
	}
	w := &witness{f: f}
	fi, err := f.Stat()
	if err != nil {
		f.Close()
		return nil, false
	}
	if fi.Size() > witnessSize {
		flag := make([]byte, 1)
		if _, err := f.ReadAt(flag, witnessSize); err != nil {
			f.Close()
			return nil, false
		}
		if flag[0] != 0 {
			return w, true
		}
	}
	if !w.writeSync(make([]byte, witnessSize), 0) || !w.writeSync([]byte{1}, witnessSize) {
		f.Close()
		return nil, false
	}
	return w, true
}

// writeSync writes b at off and makes the file durable.
func (w *witness) writeSync(b []byte, off int64) bool {
	if _, err := w.f.WriteAt(b, off); err != nil {
		return false
	}
	return syscall.Fdatasync(int(w.f.Fd())) == nil
}

// ack durably records that client c's transfer with sequence number seq committed.
func (w *witness) ack(c uint64, seq uint64) bool {
	off := int64((2*c + seq%2) * slotSize)
	w.mu.Lock()
	ok := w.writeSync([]byte{0}, off+8) && w.writeSync(encode(seq), off) &&
		w.writeSync([]byte{1}, off+8)
	w.mu.Unlock()
	return ok
}

// acked reads, per client, the largest sequence number a set flag guards (0 if none).
func (w *witness) acked() ([]uint64, bool) {
	buf := make([]byte, witnessSize)
	if _, err := w.f.ReadAt(buf, 0); err != nil {
		return nil, false
	}
	acked := make([]uint64, nClients)
	for c := uint64(0); c < nClients; c++ {
		for slot := uint64(0); slot < 2; slot++ {
			off := (2*c + slot) * slotSize
			if buf[off+8] != 0 {
				v := decode(buf[off : off+8])
				if v > acked[c] {
					acked[c] = v
				}
			}
		}
	}
	return acked, true
}

func (w *witness) close() {
	w.f.Close()
}
