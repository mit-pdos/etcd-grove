Stage **S2 (sync)** of the Go-model overlays plan (#692): `internal/sync`, `sync` and `github.com/goose-lang/primitive`. Branch `goose-model-overlay-rest-sync` (Perennial), head 66369f153, on `lean` 54a29571e plus the shared commits 3b964cf3e/5f484ea16 (split: asm allowlist, push-linkname blanking), 5dfe37eaf/1aafe42c7 (time: `gomodel.Choose`/`ChooseUint64` specs, CheckAPI without parameter names). Not to be landed by its author.

## What changed

**Today (lean):** `TrustedCode/internal/sync.lean` (106 lines: `Mutex.underlying := go.bool`, `Lock/TryLock/Unlock` over the Lean spin lock), `TrustedCode/sync.lean` (207: `runtime_Semacquire*`, `Semrelease`, `notifyList*`, `registerPoolCleanup`, `copyChecker`/`check`, `Pool.Get/Put` over the Go model package `goose/model/pool`), `Golang/Defn/Lock.lean` (39: `lock.trylock/lock/unlock`), `goose/model/pool` (Go 103 + generated/proof 400), and a field `pool_sem : goose.model.pool.Assumptions` of `go.Semantics`.

**With this branch:** `TrustedCode/internal/sync.lean`, `Golang/Defn/Lock.lean`, `goose/model/pool/**` deleted; `go.Semantics` loses `pool_sem`; `TrustedCode/sync.lean` keeps only `copyChecker`/`check` (unchanged) and the new stub `poolModelAt`.

### Became real translations
- `internal/sync.Mutex` (type: `struct{state int32; sema uint32}`, was `go.bool`), `mutexLocked`.
- `sync.notifyList` (was axiomatized: now its real struct), `sync.Pool` already was.

### Go models (trusted Go; `goose/model/overlay/{internal/sync,sync}`)
| model | why not the real Go |
|---|---|
| `internal/sync.Mutex.Lock/TryLock/Unlock` | `lockSlow`/`unlockSlow` park on bodyless runtime hooks (`runtime_SemacquireMutex`, `canSpin`, `doSpin`, `nanotime`) and read `state` with plain loads racing with the CASes; the three share the waiter/starvation protocol, so they are replaced together. Model: CAS spin on `state` 0↔1; `TryLock` may fail by `gomodel.Choose` (starvation, lost CAS); `Unlock` of an unlocked mutex → `fatal` |
| `internal/sync.fatal` | runtime push linkname, no body; unrecoverable. Model: `gomodel.Stuck()` |
| `sync.runtime_Semacquire{,WaitGroup,RWMutexR,RWMutex}` | no body (runtime push linknames). Model: the runtime's `cansemacquire` loop over `sync/atomic`, retried (spins where Go parks) |
| `sync.runtime_Semrelease` | no body. Model: `atomic.AddUint32(s, 1)` |
| `sync.runtime_notifyList{Add,Wait,NotifyAll,NotifyOne,Check}` | no body (runtime push linknames). Model: the runtime's own ticket algorithm on the real `notifyList` fields: `Add` = `atomic.AddUint32(&l.wait, 1) - 1`; `Wait(t)` spins while `int32(t - atomic.LoadUint32(&l.notify)) >= 0` (the runtime's `less`); `NotifyOne`/`NotifyAll` advance `l.notify` by one / to `l.wait` by a CAS loop (Go does it under the list's lock), returning when `notify == wait`; `Check` empty. **Revised after the adversarial review:** the first version's `Wait` returned at once, so `mu.Lock(); c.Wait()` with no signaller returned in the model while Go blocks forever (Go's `Cond` has no spurious wakeups): more defined than Go, unsound |
| `sync.runtime_registerPoolCleanup` | no body; the model has no GC. Empty |
| `sync.Pool.Get/Put` | `indexLocal` converts `uintptr` → `unsafe.Pointer` (stuck), `poolDequeue` stores an `any` through an `eface` cast, `runtime_procPin` has no body. Model (absorbs `goose/model/pool`): a `poolModel{mu Mutex; items []any}` hung off `p.local` (lazily installed by CAS from nil, race-free on a zero `Pool`); `Put` may drop (`Choose`); `Get` may miss (`Choose`) or takes an arbitrary element (`ChooseUint64`), then Go's own `New` fallback |

<details><summary>Each model next to the real Go (<code>etc/trusted-delta.py 54a29571e..HEAD</code>)</summary>

#### Go model overlays (TRUSTED: model Go is reviewed as Go, rule R12)

For each replaced declaration: every behaviour of the real one (gc, linux/amd64, the pinned Go), under every use by the program and the real package, must be a behaviour of the model's translation. Compare the two sources line by line; every `gomodel.Choose`/`ChooseUint64`/`Stuck` needs a reason in the doc comment.

### Perennial/Code/internal/sync.toml  (package `internal/sync`)

- `[model]` before: none
- `[model]` after:  dir = 'goose/model/overlay/internal/sync', replaces = ['Mutex.Lock', 'Mutex.TryLock', 'Mutex.Unlock', 'fatal'], added_methods = []
- model files: goose/model/overlay/internal/sync/mutex.go; changed: goose/model/overlay/internal/sync/mutex.go

#### `internal/sync.Mutex.Lock` (new)

Model (goose/model/overlay/internal/sync/mutex.go:13):

```go
// MODEL: Go's Lock is a compare-and-swap of state from 0 to mutexLocked, and
// on failure lockSlow, which spins and parks on the runtime's semaphore
// (runtime_SemacquireMutex, runtime_canSpin, runtime_doSpin,
// runtime_nanotime, all without a Go body) and records waiters, wakeups and
// starvation in state, read with plain loads that race with the
// compare-and-swaps. Goose translates lockSlow, but the hooks have no body and
// the racy reads are outside what the sequentially consistent semantics
// models; and the protocol in state is shared with TryLock and Unlock, so
// they are replaced together. The model keeps state at 0 (unlocked) or
// mutexLocked and spins on the fast path's compare-and-swap until it
// succeeds: Lock returns exactly when it takes the mutex, as in Go; a
// spinning model goroutine where Go's parks is a schedule with the same
// results (the model has no fairness and no starvation mode, which only
// order waiters). A goroutine that never gets the mutex spins forever where
// Go's parks forever: spinning for parking is partial correctness, and Go's
// deadlock detector (a global deadlock becomes the fatal throw "all
// goroutines are asleep") is not modelled (docs/KNOWN_LIMITATIONS.md).
func (m *Mutex) Lock() {
	for !atomic.CompareAndSwapInt32(&m.state, 0, mutexLocked) {
	}
}
```

Real (`go doc -u -src internal/sync.Mutex.Lock`):

```go
package sync // import "internal/sync"

// Lock locks m.
//
// See package [sync.Mutex] documentation.
func (m *Mutex) Lock() {
	// Fast path: grab unlocked mutex.
	if atomic.CompareAndSwapInt32(&m.state, 0, mutexLocked) {
		if race.Enabled {
			race.Acquire(unsafe.Pointer(m))
		}
		return
	}
	// Slow path (outlined so that the fast path can be inlined)
	m.lockSlow()
}
```

#### `internal/sync.Mutex.TryLock` (new)

Model (goose/model/overlay/internal/sync/mutex.go:35):

```go
// MODEL: Go's TryLock returns false if state is locked or starving, or if its
// compare-and-swap of state to locked loses to a concurrent change, else
// true. The model's state has no starvation bit and no waiters, so where Go
// fails on an unlocked mutex (starvation mode, or a waiter changing state),
// the model fails by an arbitrary choice (gomodel.Choose); otherwise it is the
// compare-and-swap of 0 to mutexLocked. It thus returns false in every case
// Go does, and true only when it took the mutex, as in Go.
func (m *Mutex) TryLock() bool {
	if gomodel.Choose() {
		return false
	}
	return atomic.CompareAndSwapInt32(&m.state, 0, mutexLocked)
}
```

Real (`go doc -u -src internal/sync.Mutex.TryLock`):

```go
package sync // import "internal/sync"

// TryLock tries to lock m and reports whether it succeeded.
//
// See package [sync.Mutex] documentation.
func (m *Mutex) TryLock() bool {
	old := m.state
	if old&(mutexLocked|mutexStarving) != 0 {
		return false
	}

	// There may be a goroutine waiting for the mutex, but we are
	// running now and can try to grab the mutex before that
	// goroutine wakes up.
	if !atomic.CompareAndSwapInt32(&m.state, old, old|mutexLocked) {
		return false
	}

	if race.Enabled {
		race.Acquire(unsafe.Pointer(m))
	}
	return true
}
```

#### `internal/sync.Mutex.Unlock` (new)

Model (goose/model/overlay/internal/sync/mutex.go:49):

```go
// MODEL: Go's Unlock subtracts mutexLocked from state and, if waiters remain,
// wakes one (unlockSlow, through runtime_Semrelease); on an unlocked mutex it
// calls fatal("sync: unlock of unlocked mutex"). The model's state has no
// waiters (a spinning Lock sees the 0), so Unlock is the compare-and-swap of
// mutexLocked to 0, and fatal where it fails, that is where the mutex is not
// locked.
func (m *Mutex) Unlock() {
	if !atomic.CompareAndSwapInt32(&m.state, mutexLocked, 0) {
		fatal("sync: unlock of unlocked mutex")
	}
}
```

Real (`go doc -u -src internal/sync.Mutex.Unlock`):

```go
package sync // import "internal/sync"

// Unlock unlocks m.
//
// See package [sync.Mutex] documentation.
func (m *Mutex) Unlock() {
	if race.Enabled {
		_ = m.state
		race.Release(unsafe.Pointer(m))
	}

	// Fast path: drop lock bit.
	new := atomic.AddInt32(&m.state, -mutexLocked)
	if new != 0 {
		// Outlined slow path to allow inlining the fast path.
		// To hide unlockSlow during tracing we skip one extra frame when tracing GoUnblock.
		m.unlockSlow(new)
	}
}
```

#### `internal/sync.fatal` (new)

Model (goose/model/overlay/internal/sync/mutex.go:61):

```go
// MODEL: Go's fatal (a runtime push linkname, no Go body) prints the message
// and ends the program, and recover cannot catch it. The model has no
// behaviour there (gomodel.Stuck): a verified program never calls it.
func fatal(string) {
	gomodel.Stuck()
}
```

Real (`go doc -u -src internal/sync.fatal`):

```go
package sync // import "internal/sync"

//go:linkname fatal
func fatal(string)
```

### Perennial/Code/sync.toml  (package `sync`)

- `[model]` before: none
- `[model]` after:  dir = 'goose/model/overlay/sync', replaces = ['runtime_Semacquire', 'runtime_SemacquireWaitGroup', 'runtime_SemacquireRWMutexR', 'runtime_SemacquireRWMutex', 'runtime_Semrelease', 'runtime_notifyListAdd', 'runtime_notifyListWait', 'runtime_notifyListNotifyAll', 'runtime_notifyListNotifyOne', 'runtime_notifyListCheck', 'runtime_registerPoolCleanup', 'Pool.Get', 'Pool.Put'], added_methods = []
- model files: goose/model/overlay/sync/pool.go, goose/model/overlay/sync/runtime.go; changed: goose/model/overlay/sync/pool.go, goose/model/overlay/sync/runtime.go

#### `sync.Pool.Get` (new)

Model (goose/model/overlay/sync/pool.go:75):

```go
// MODEL: Go's Get pins the goroutine to its P and takes the P's private
// value, else pops its shared chain, else steals from other Ps and the
// victim cache (getSlow); if it found nothing and New is not nil, it returns
// New(). Goose translates it but is stuck as for Put. The model's search
// takes an arbitrary element of the pool's state or nothing, even when the
// state is not empty (gomodel.Choose: Go's search may miss values in other
// Ps' chains or dropped by the GC, and gomodel.ChooseUint64: which value it
// finds); the rest, calling New, is Go's.
func (p *Pool) Get() any {
	s := poolModelOf(p)
	var x any
	s.mu.Lock()
	n := uint64(len(s.items))
	if n != 0 && !gomodel.Choose() {
		i := gomodel.ChooseUint64() % n
		x = s.items[i]
		s.items[i] = s.items[n-1]
		s.items = s.items[:n-1]
	}
	s.mu.Unlock()
	if x == nil && p.New != nil {
		x = p.New()
	}
	return x
}
```

Real (`go doc -u -src sync.Pool.Get`):

```go
package sync // import "sync"

// Get selects an arbitrary item from the [Pool], removes it from the
// Pool, and returns it to the caller.
// Get may choose to ignore the pool and treat it as empty.
// Callers should not assume any relation between values passed to [Pool.Put] and
// the values returned by Get.
//
// If Get would otherwise return nil and p.New is non-nil, Get returns
// the result of calling p.New.
func (p *Pool) Get() any {
	if race.Enabled {
		race.Disable()
	}
	l, pid := p.pin()
	x := l.private
	l.private = nil
	if x == nil {
		// Try to pop the head of the local shard. We prefer
		// the head over the tail for temporal locality of
		// reuse.
		x, _ = l.shared.popHead()
		if x == nil {
			x = p.getSlow(pid)
		}
	}
	runtime_procUnpin()
	if race.Enabled {
		race.Enable()
		if x != nil {
			race.Acquire(poolRaceAddr(x))
		}
	}
	if x == nil && p.New != nil {
		x = p.New()
	}
	return x
}
```

#### `sync.Pool.Put` (new)

Model (goose/model/overlay/sync/pool.go:52):

```go
// MODEL: Go's Put ignores nil and otherwise pins the goroutine to its P and
// stores x in that P's private slot or pushes it onto the P's lock-free
// shared chain; the GC later moves the per-P pools to the victim cache and
// then drops them. Goose translates it, but the translation is stuck at
// indexLocal's conversion of a uintptr back to an unsafe.Pointer (pointer
// arithmetic) and at poolDequeue's store of an any through an
// unsafe.Pointer to its eface; runtime_procPin, which keeps the goroutine on
// its P, has no Go body. The model ignores nil as Go does, and otherwise
// adds x to the pool's state or drops it (gomodel.Choose: the GC may drop it
// in Go before any Get).
func (p *Pool) Put(x any) {
	if x == nil {
		return
	}
	s := poolModelOf(p)
	if gomodel.Choose() {
		return
	}
	s.mu.Lock()
	s.items = append(s.items, x)
	s.mu.Unlock()
}
```

Real (`go doc -u -src sync.Pool.Put`):

```go
package sync // import "sync"

// Put adds x to the pool.
func (p *Pool) Put(x any) {
	if x == nil {
		return
	}
	if race.Enabled {
		if runtime_randn(4) == 0 {
			// Randomly drop x on floor.
			return
		}
		race.ReleaseMerge(poolRaceAddr(x))
		race.Disable()
	}
	l, _ := p.pin()
	if l.private == nil {
		l.private = x
	} else {
		l.shared.pushHead(x)
	}
	runtime_procUnpin()
	if race.Enabled {
		race.Enable()
	}
}
```

#### `sync.runtime_Semacquire` (new)

Model (goose/model/overlay/sync/runtime.go:13):

```go
// MODEL: Go's runtime_Semacquire (runtime/sema.go, semacquire1) waits until
// *s > 0 and decrements it, trying first
//
//	func cansemacquire(addr *uint32) bool {
//		for {
//			v := atomic.Load(addr)
//			if v == 0 {
//				return false
//			}
//			if atomic.Cas(addr, v, v-1) {
//				return true
//			}
//		}
//	}
//
// and, while that fails, parking on a queue that runtime_Semrelease wakes. The
// model is cansemacquire's loop, retried until it succeeds: it returns exactly
// when it has decremented a positive *s, as Go's does; a model goroutine
// spinning where Go's parks is a schedule with the same results (the queue
// only orders the waiters). A goroutine that never acquires spins forever
// where Go's parks forever: spinning for parking is partial correctness, and
// Go's deadlock detector (a global deadlock becomes the fatal throw "all
// goroutines are asleep") is not modelled (docs/KNOWN_LIMITATIONS.md).
func runtime_Semacquire(s *uint32) {
	for {
		v := atomic.LoadUint32(s)
		if v == 0 {
			continue
		}
		if atomic.CompareAndSwapUint32(s, v, v-1) {
			return
		}
	}
}
```

Real (`go doc -u -src sync.runtime_Semacquire`):

```go
package sync // import "sync"

// Semacquire waits until *s > 0 and then atomically decrements it.
// It is intended as a simple sleep primitive for use by the synchronization
// library and should not be used directly.
func runtime_Semacquire(s *uint32)
```

#### `sync.runtime_SemacquireRWMutex` (new)

Model (goose/model/overlay/sync/runtime.go:61):

```go
// MODEL: as runtime_Semacquire (see runtime_SemacquireRWMutexR).
func runtime_SemacquireRWMutex(s *uint32, lifo bool, skipframes int) {
	runtime_Semacquire(s)
}
```

Real (`go doc -u -src sync.runtime_SemacquireRWMutex`):

```go
package sync // import "sync"

func runtime_SemacquireRWMutex(s *uint32, lifo bool, skipframes int)
```

#### `sync.runtime_SemacquireRWMutexR` (new)

Model (goose/model/overlay/sync/runtime.go:55):

```go
// MODEL: as runtime_Semacquire: lifo and skipframes only order the waiters
// and select the profiled stack frames.
func runtime_SemacquireRWMutexR(s *uint32, lifo bool, skipframes int) {
	runtime_Semacquire(s)
}
```

Real (`go doc -u -src sync.runtime_SemacquireRWMutexR`):

```go
package sync // import "sync"

// Semacquire(RW)Mutex(R) is like Semacquire, but for profiling contended
// Mutexes and RWMutexes.
// If lifo is true, queue waiter at the head of wait queue.
// skipframes is the number of frames to omit during tracing, counting from
// runtime_SemacquireMutex's caller.
// The different forms of this function just tell the runtime how to present
// the reason for waiting in a backtrace, and is used to compute some metrics.
// Otherwise they're functionally identical.
func runtime_SemacquireRWMutexR(s *uint32, lifo bool, skipframes int)
```

#### `sync.runtime_SemacquireWaitGroup` (new)

Model (goose/model/overlay/sync/runtime.go:48):

```go
// MODEL: as runtime_Semacquire: Go's differs only in the reason it reports
// for a parked goroutine and in synctest's durable blocking, which the model
// does not observe.
func runtime_SemacquireWaitGroup(s *uint32, synctestDurable bool) {
	runtime_Semacquire(s)
}
```

Real (`go doc -u -src sync.runtime_SemacquireWaitGroup`):

```go
package sync // import "sync"

// SemacquireWaitGroup is like Semacquire, but for WaitGroup.Wait.
func runtime_SemacquireWaitGroup(s *uint32, synctestDurable bool)
```

#### `sync.runtime_Semrelease` (new)

Model (goose/model/overlay/sync/runtime.go:66):

```go
// MODEL: Go's runtime_Semrelease (semrelease1) atomically increments *s and
// wakes a waiter if there is one (handing it the count directly if handoff);
// the model's waiters spin, so it is the increment.
func runtime_Semrelease(s *uint32, handoff bool, skipframes int) {
	atomic.AddUint32(s, 1)
}
```

Real (`go doc -u -src sync.runtime_Semrelease`):

```go
package sync // import "sync"

// Semrelease atomically increments *s and notifies a waiting goroutine
// if one is blocked in Semacquire.
// It is intended as a simple wakeup primitive for use by the synchronization
// library and should not be used directly.
// If handoff is true, pass count directly to the first waiter.
// skipframes is the number of frames to omit during tracing, counting from
// runtime_Semrelease's caller.
func runtime_Semrelease(s *uint32, handoff bool, skipframes int)
```

#### `sync.runtime_notifyListAdd` (new)

Model (goose/model/overlay/sync/runtime.go:73):

```go
// MODEL: Go's runtime_notifyListAdd (runtime/sema.go, notifyListAdd) is
//
//	return l.wait.Add(1) - 1
//
// the next ticket of the list, taken atomically; the model is the same over
// sync/atomic (wait is the runtime's atomic.Uint32, a uint32 in sync's copy of
// the type).
func runtime_notifyListAdd(l *notifyList) uint32 {
	return atomic.AddUint32(&l.wait, 1) - 1
}
```

Real (`go doc -u -src sync.runtime_notifyListAdd`):

```go
package sync // import "sync"

// See runtime/sema.go for documentation.
func runtime_notifyListAdd(l *notifyList) uint32
```

#### `sync.runtime_notifyListCheck` (new)

Model (goose/model/overlay/sync/runtime.go:137):

```go
// MODEL: Go's runtime_notifyListCheck throws if size is not the runtime's
// size of notifyList; the type is the real one, so its size is the runtime's,
// and the check passes.
func runtime_notifyListCheck(size uintptr) {
}
```

Real (`go doc -u -src sync.runtime_notifyListCheck`):

```go
package sync // import "sync"

// Ensure that sync and runtime agree on size of notifyList.
func runtime_notifyListCheck(size uintptr)
```

#### `sync.runtime_notifyListNotifyAll` (new)

Model (goose/model/overlay/sync/runtime.go:104):

```go
// MODEL: Go's runtime_notifyListNotifyAll (notifyListNotifyAll) returns if
// l.wait == l.notify (no waiter), and otherwise, under the list's lock, sets
// l.notify to l.wait and readies every parked waiter. The model reads both and
// sets l.notify with a compare-and-swap, retried if l.notify changed in
// between: the store linearizes at the compare-and-swap, as Go's does under
// the lock (the lock only orders the notify calls, which the compare-and-swap
// also does). The waiters are readied by the new l.notify (see
// runtime_notifyListWait).
func runtime_notifyListNotifyAll(l *notifyList) {
	for {
		n := atomic.LoadUint32(&l.notify)
		w := atomic.LoadUint32(&l.wait)
		if n == w || atomic.CompareAndSwapUint32(&l.notify, n, w) {
			return
		}
	}
}
```

Real (`go doc -u -src sync.runtime_notifyListNotifyAll`):

```go
package sync // import "sync"

// See runtime/sema.go for documentation.
func runtime_notifyListNotifyAll(l *notifyList)
```

#### `sync.runtime_notifyListNotifyOne` (new)

Model (goose/model/overlay/sync/runtime.go:122):

```go
// MODEL: Go's runtime_notifyListNotifyOne (notifyListNotifyOne) returns if
// l.wait == l.notify (no waiter), and otherwise, under the list's lock,
// increments l.notify and readies the waiter holding the old value as its
// ticket, if it has parked yet (if not, its Wait sees the ticket notified and
// returns at once). The model is the same increment by compare-and-swap,
// retried if l.notify changed in between (as for NotifyAll).
func runtime_notifyListNotifyOne(l *notifyList) {
	for {
		n := atomic.LoadUint32(&l.notify)
		if n == atomic.LoadUint32(&l.wait) || atomic.CompareAndSwapUint32(&l.notify, n, n+1) {
			return
		}
	}
}
```

Real (`go doc -u -src sync.runtime_notifyListNotifyOne`):

```go
package sync // import "sync"

// See runtime/sema.go for documentation.
func runtime_notifyListNotifyOne(l *notifyList)
```

#### `sync.runtime_notifyListWait` (new)

Model (goose/model/overlay/sync/runtime.go:84):

```go
// MODEL: Go's runtime_notifyListWait (notifyListWait) returns at once if
// ticket t has been notified, less(t, l.notify) with
//
//	func less(a, b uint32) bool {
//		return int32(a-b) < 0
//	}
//
// and otherwise parks until a notify call readies it, which the notify calls
// do exactly when they advance l.notify past t (NotifyOne readies the waiter
// whose ticket is the old l.notify, NotifyAll every waiter). The model spins
// on the same test, reading l.notify atomically: it returns exactly when Go's
// can. A goroutine that is never notified spins forever where Go's parks
// forever: spinning for parking is partial correctness, and Go's deadlock
// detector (a global deadlock becomes the fatal throw "all goroutines are
// asleep") is not modelled (docs/KNOWN_LIMITATIONS.md).
func runtime_notifyListWait(l *notifyList, t uint32) {
	for int32(t-atomic.LoadUint32(&l.notify)) >= 0 {
	}
}
```

Real (`go doc -u -src sync.runtime_notifyListWait`):

```go
package sync // import "sync"

// See runtime/sema.go for documentation.
func runtime_notifyListWait(l *notifyList, t uint32)
```

#### `sync.runtime_registerPoolCleanup` (new)

Model (goose/model/overlay/sync/pool.go:101):

```go
// MODEL: Go's runtime_registerPoolCleanup (a runtime push linkname, no Go
// body) records poolCleanup for the GC to call at the start of each cycle;
// poolCleanup moves the per-P pools to the victim cache. The model has no GC,
// and its pools' state is not in the per-P pools, which only the replaced
// Get and Put used, so recording it changes nothing.
func runtime_registerPoolCleanup(cleanup func()) {
}
```

Real (`go doc -u -src sync.runtime_registerPoolCleanup`):

```go
package sync // import "sync"

// Implemented in runtime.
func runtime_registerPoolCleanup(cleanup func())
```

Additions (no claim of their own; a primitive stub carries the TrustedCode claim, R2; an added method must match `added_methods`):

- `poolModel` (type, goose/model/overlay/sync/pool.go:15, new)
- `poolModelOf` (func, goose/model/overlay/sync/pool.go:28, new)
- `poolModelAt` (func, goose/model/overlay/sync/pool.go:41, new); PRIMITIVE STUB (in `trusted`: its Lean `.impl` in Perennial/TrustedCode is the model)

</details>

### New primitive (stub)
`sync.poolModelAt(l unsafe.Pointer) *poolModel` (`TrustedCode/sync.lean`):
```lean
def poolModelAt.impl : val := λ: "l", "l"
```
Go body `return (*poolModel)(l)`. R2 run (moved to `translate`): goose emits `Convert unsafe.Pointer (*poolModel)`, which is stuck: the semantics converts an `unsafe.Pointer` only to a pointer to a plain type (`Golang/Defn/Plain.lean`, `convert_unsafe_to_pointer`), and `poolModel` holds a `Mutex` and a slice. Identity is right because `p.local` is unexported and, with `Get`/`Put` modelled, only `poolModelOf` writes it, always with a `*poolModel`. Spec `sync.poolModelAt.spec` (`{{ True }} … {{ RET #l; True }}`), proved.

### Stays hand-written Lean
- `sync.copyChecker`/`check` (unchanged): a Go model `struct{ p unsafe.Pointer }` changes an unexported type's kind and underlying type, which the overlay's API check refuses. Follow-up (a'): let the check accept that for an unexported type that no exported API exposes by kind (reachability), keeping comparability identical (`Cond.checker` sits in the exported, comparable `Cond`).
- `primitive.Mutex`, `Lock`, `Unlock`, `Assume`: the overlay cannot replace a file of a module under GOMODCACHE, where goose finds `primitive` (`go build -overlay`: `go: overlay contains a replacement for …/pkg/mod/github.com/goose-lang/primitive@…/prims.go. Files beneath GOMODCACHE (…) must not be replaced.`). The spin lock `lock.lock`/`lock.unlock` moved from `Golang/Defn/Lock.lean` to `TrustedCode/github_com/goose_lang/primitive.lean` **unchanged** (a relocation, not a retirement; `lock.trylock`, unused, dropped). Follow-up (B): vendor `primitive` (or move it into Perennial's module) so that it can take an overlay; a Go model of it is parked in `gmr-sync/pending-primitive/`.
- `primitive.Assume` keeps its documented divergence (Go panics, the model loops): the library's explicit verification assumption, now said so in its docstring. Pre-existing.
- **Deleted dead `.impl`s** (in the WIP commit 68f0cdc43, which also relocated the spin lock): `primitive.Assert/Exit/Sleep/TimeNow/AfterFunc/Linearize/ResolveProph/Millisecond/Second` from `TrustedCode/github_com/goose_lang/primitive.lean`, and `lock.trylock` from the old `Golang/Defn/Lock.lean`. None was reachable: no generated code names them (goose emits them only for a `trusted` entry, and `primitive.toml` lists none of them), and no proof unfolds them. Trust shrinks; nothing else changes.

## Premise and statement changes
- **Removed premise:** `go.Semantics.pool_sem : github_com.mit_pdos.perennial.goose.model.pool.Assumptions` (the old Pool model's package assumptions), a field of the class every result takes. Strengthening.
- **Forced restatement** of a lemma (the type changed): `internal.sync.init_lock` (Proof/internal/sync/Base) takes `m ↦ zero_val internal.sync.Mutex` instead of `m ↦ false`. The Bool spin lock's lemmas are renamed (`init_lock` → `init_spinLock`, `isLock`/`ownLock` → `isSpinLock`/`ownSpinLock`, `wp_lock_lock`/`wp_lock_unlock` keep their names). No spec changes: `sync.init_Mutex`, `isMutex`, `ownMutex`, every `sync`/`internal/sync`/`primitive` spec are as on lean (the plan's `primitive.init_Mutex` restatement did not happen: `primitive.Mutex` stays `go.bool`).
- **Internal sync specs restated (notifyList):** `runtime_notifyList{Add,Wait,NotifyAll,NotifyOne}.spec` were `{{ isPkgInit sync ∗ l ↦{dq} l_v }} … {{ RET …; l ↦{dq} l_v }}`; now `{{ isPkgInit sync ∗ isNotifyList l }} … {{ RET …; True }}`, with the new sealed `sync.isNotifyList l` (an invariant owning `l.wait` and `l.notify`). These are the specs of sync's unexported runtime hooks, used only by `Cond`'s proofs. `isCond`'s field `Hnotify` changes from `c.notify ↦□ zero_val notifyList` (with a FIXME saying it was inaccurate) to `isNotifyList c.notify`, inside the sealed `isCond`; `NewCond` allocates the invariant. The `Cond.Wait/Signal/Broadcast` and `NewCond` statements are unchanged. etcd-grove: `workqueue/Defs.lean` (`isCond_L`, destructures `isCondDef` by position) and `schedule/fifo__executeJob.lean` (rebuilds `isCond` by `iframe #`) keep working as long as the field order is kept (it is).
- `isLock`/`ownLock` (internal/sync) now over `m.state ↦ (0|1 : w32)` (1/4 in the invariant, 3/4 for the holder); the Bool spin lock is `isSpinLock`/`ownSpinLock` (`Golang/Theory/Lock.lean`), used by `primitive.isMutex` and the channel model.

## Axioms
`#print axioms` (VM, at 2125733d6, and again at 66369f153) of all 51 linked results of `internal/sync`, `sync` and `primitive` (`internal.sync.Mutex.wp_{Lock,TryLock,Unlock}`, `sync.Pool.wp_{Get,Put}`, `sync.wp_poolModel{Of,At}`, `sync.wp_runtime_*`, `sync.Mutex.*`, `RWMutex`, `WaitGroup`, `Cond`, `Once`, `wp_initialize'`, `primitive.*`) and of `wp_testMutexLiteral` (and `Cond.wp_Wait_with`): each is exactly `[propext, Classical.choice, Quot.sound]`. No new Lean axiom, no `sorry` (the generated `sorry -- axiomatized type` instances of `HashTrieMap`/`hashFunc` are not reached).

## Evidence
- **Builds (VM):** every module of the `Perennial` library and `PerennialMeta` (2429 modules, `find Perennial -name '*.lean'`, in 4 chunks of ≤800): all exit 0 at 2125733d6, and again at 66369f153 (after the notify-list fix). `etc/meta-lib.py --check` clean.
- **`go test ./...` in `goose/`:** pass.
- **`etc/model-tests.sh`** (Go's own tests under the overlay): `internal/sync` in full; `goose/model/overlaytests` (new: `Cond.Wait` without a signal blocks, `Signal` wakes exactly one, a `Signal` before any waiter is lost; timeout-based, pass on real Go too); `sync` in full (including `TestCondSignal`, `TestCondBroadcast`, `TestRace`, which the faithful notify list now passes) except, each with its reason in the script:
  - `TestMutexMisuse`: an `Unlock` of an unlocked `Mutex` reaches `fatal`, whose model is `gomodel.Stuck` (blocks in gc), where Go ends the process (the test runs a subprocess and expects the crash);
  - `TestPool`, `TestPoolGC`, `TestPoolRelease`: they rely on the GC clearing pools; the model has no GC, so its `Get` may return a value Go's GC would have dropped.
- **R2 goose runs:** the real `sync` with `Pool.Get/Put`, their helpers and `copyChecker` in `translate` (predecessor, `gmr-sync/exp/out`): stuck at `indexLocal`'s `uintptr` → `unsafe.Pointer`, `poolDequeue`'s `eface` cast, `Convert unsafe.Pointer uintptr` and `*copyChecker` → `*uintptr` (`exp/out/sync.lean:389-392`); `poolModelAt` in `translate`: `Convert unsafe.Pointer (*poolModel)` (stuck, above). `internal/sync`'s `lockSlow`/`unlockSlow` translate but call the bodyless runtime hooks.

## etcd-grove at the pin bump
Seven etcd-grove files unfold the old lock (`lock.lock`/`lock.unlock`, `isLockDef`/`ownLockDef`, a Bool `state`); none changes a top-level statement. etcd-grove pins Perennial 04b42a139, where `sync.Mutex` itself was `go.bool`, so some of this is from the intermediate `sync.Mutex` struct change on lean, not only from this branch.
- `examples/raft/kvreconf/MutexFresh.lean` (`wp_Mutex_Lock_fresh`): pre `m ↦ false` becomes `m ↦ zero_val sync.Mutex` (or its `mu.state ↦ W32 0`); the proof follows the model (`sync.Mutex.Lock` → `internal/sync` CAS on `state` 0→1, as `wp_Lock_owned` in Perennial's `testMutexLiteral.lean`) and allocates `internal.sync.lockInv` at `W32 1` (unfold `isLockDef`/`ownLockDef`: now on `structFieldRef internal.sync.Mutex "state"`).
- `bbolt/Open/MutexOwn.lean` and `storage/backend/NewLemmas.lean` (`Lock`/`Unlock` of an owned mutex): the same, CAS 0→1 and 1→0 on `state` (a `w32` points-to instead of a Bool). The pair `wp_Lock_owned`/`wp_Unlock_owned` of Perennial's `testMutexLiteral.lean` is the template (and could move to `Proof/sync` as the owned-mutex specs both files propose).
- `storage/mvcc/PlainRWMutex.lean`: `RWMutex.w`'s lock/unlock on owned memory, same change; its values `rwZero`/`rwR1`/`rwW` carry `w' : sync.Mutex` (a struct) instead of a Bool (`rwW.w' = true` → `rwW.w'.mu'.state' = W32 1`).
- `storage/mvcc/RWMutexWLocked.lean` (`init_lock_locked`: `m ↦ true` ⊢ `isLock m R ∗ ownLock m`): restated over `m.state ↦ W32 1` and `internal.sync.lockInv`.
- `bbolt/Commit/CheckChan.lean`: `init_lock` on the channel model's `primitive.Mutex` → `init_spinLock` (rename only).
- `storage/backend/MutexLit.lean` (axiom `wp_mutexLit`: `sync.Mutex{}` returns `#false`) and `Proof/sync/MutexLitSemantics.lean` (a premise class): **must be deleted at the bump, not ported.** `sync.Mutex{}` is now a struct literal with a step rule, so the gap they fill is gone, and `wp_mutexLit` would state a wrong value (`#false` for a struct). Their users (`backend/newBackend.lean`, `client_go/util/workqueue/newQueue.lean`, its `Link.lean`) step the literal instead: an axiom and a premise fewer.

## Review (`review-trusted --fix`)
Verdict: **OK (4 NOTEs) after one BLOCK fixed** (the notify list, N3: my review missed it, the lead's adversarial review found it). Fixed during the review: stale comments in `Perennial/Code/sync.toml` and `TrustedCode/sync.lean` (they still called `copyChecker` a Go model).
- N1 [R12/R4] `internal/sync.Mutex.Lock`, `runtime_Semacquire*`, `runtime_notifyListWait` and `primitive`'s `lock.lock` spin where Go parks: same results under every schedule, and a goroutine never woken spins forever where Go's parks forever. Their MODEL comments (and the Lean docstring of `lock.lock`) now say this is partial correctness and that Go's deadlock detector (a global deadlock becomes the fatal throw "all goroutines are asleep") is not modelled; `docs/KNOWN_LIMITATIONS.md` has a new entry, "Blocking and deadlock", with the witness `mu.Lock(); sync.NewCond(&mu).Wait()`.
- N2 [R2] `poolModelAt` stub: goose translates the real body; the stuck point is the semantics (`Convert unsafe.Pointer (*poolModel)`, only plain element types). A general rule would need the pointer's provenance; the stub is the narrow, lead-approved form, with its identity argument in the docstring.
- ~~N3~~ **Found by the adversarial review (lead's sub-agent, `gmr-adv-sync/`), fixed:** my review graded the no-op `runtime_notifyListWait` as "more behaviours, allowed"; it is wrong, Go's `Wait` never returns without a notify, so the model was more defined than Go (R4 BLOCK). Now the faithful ticket model above; `goose/model/overlaytests/cond_test.go` checks that `Wait` without a signal blocks, under the overlay and on real Go.
- N4 inherited: `copyChecker`/`check` (Lean), `primitive.Mutex`/`Assume` (Lean, GOMODCACHE), `Assume`'s documented divergence.
- N5 [R12] `TryLock`'s `gomodel.Choose` failure, `Pool`'s `Choose`/`ChooseUint64`, `fatal`'s `Stuck`: each has its reason in the MODEL comment.
- Skipped: the adversarial sub-agent of step 4 (the lead allows no sub-agents now); `etc/land.sh mark-reviewed` (nothing lands).

## Open items / follow-ups
- (a') `copyChecker` as a Go model, once the overlay's API check accepts a kind change of an unexported type (comparability kept).
- (B) `primitive` under an overlay (vendor it or move it into Perennial's module); the parked model is in `gmr-sync/pending-primitive/`.
- etcd-grove at the bump: the seven files above, and delete `wp_mutexLit` + `MutexLitSemantics`.
