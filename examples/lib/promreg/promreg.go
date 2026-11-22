// Package promreg is a model of the default registry of prometheus's client_golang v1.24.1
// (`prometheus/registry.go`), the trusted model of `prometheus.Register`, `prometheus.MustRegister`
// and the registry part of the package's initialization (notes/prom-registry.md).
//
// It is client_golang's `Registry.Register` (registry.go:283-376) over the descriptors a collector
// describes, given as values (`Desc`: what Register reads of each `*Desc` its `Describe` sends), and
// the state that decides whether a later registration fails: the registered descriptor IDs
// (`descIDs`), the label-name-and-help hash of each registered fully-qualified name
// (`dimHashesByName`) and the registered collector IDs (`collectorsByID`'s keys). Its differences
// from client_golang, outside what Register decides (`model_test.go` checks the decisions and the
// states against the real registry):
//   - Register returns a code, not an error value (the glue, TrustedCode/github_com/prometheus/
//     client_golang/prometheus.lean, makes a non-nil error of any code but OK);
//   - the collectors themselves are not kept (`collectorsByID` is a set, `uncheckedCollectors` is
//     not kept): only Gather and Unregister read them, which the model does not have;
//   - the lock is a sync.Mutex (client_golang's is a sync.RWMutex whose writer lock Register takes).
//
// `SeedBuiltins` is the state client_golang's `init` (registry.go: `MustRegister(NewProcessCollector(
// ProcessCollectorOpts{}))`, `MustRegister(NewGoCollector())`) leaves in the empty default registry,
// on configuration C (Linux, amd64, Go 1.27.3: the Go collector's `go_info` carries the runtime's
// version as a const label, and the process collector's descriptors are Linux's);
// `TestBuiltins` checks it against the real default registry.
package promreg

import "sync"

// Desc is what Registry.Register reads of a descriptor (`desc.go`'s `Desc`): its `id`, `fqName`,
// `dimHash`, and whether its `err` is non-nil.
type Desc struct {
	ID      uint64
	FQName  string
	DimHash uint64
	Invalid bool
}

// The outcomes of Register: OK (`nil`), or the error client_golang returns, by its check.
const (
	OK                   uint64 = 0 // registered, or an unchecked collector (no descriptor)
	ErrInvalid           uint64 = 1 // "descriptor %s is invalid"
	ErrDims              uint64 = 2 // "a previously registered descriptor with the same fully-qualified name ..."
	ErrNewDims           uint64 = 3 // "descriptors reported by collector have inconsistent label names ..."
	ErrAlreadyRegistered uint64 = 4 // AlreadyRegisteredError
	ErrDuplicateDesc     uint64 = 5 // "descriptor %s already exists with the same fully-qualified name and const label values"
)

// Registry is client_golang's `Registry` as Register reads and writes it.
type Registry struct {
	mu              sync.Mutex
	descIDs         map[uint64]bool
	dimHashesByName map[string]uint64
	collectorsByID  map[uint64]bool
}

// NewRegistry is client_golang's `NewRegistry` (registry.go:68-74): an empty registry.
func NewRegistry() *Registry {
	return &Registry{
		descIDs:         make(map[uint64]bool),
		dimHashesByName: make(map[string]uint64),
		collectorsByID:  make(map[uint64]bool),
	}
}

// Register is client_golang's `(*Registry).Register` (registry.go:283-376) of a collector whose
// `Describe` sends `descs`, in order.
func (r *Registry) Register(descs []Desc) uint64 {
	var newIDs []uint64
	newSeen := make(map[uint64]bool)
	newDims := make(map[string]uint64)
	var newNames []string
	var collectorID uint64
	duplicate := false
	r.mu.Lock()
	for _, d := range descs {
		if d.Invalid {
			r.mu.Unlock()
			return ErrInvalid
		}
		if r.descIDs[d.ID] {
			duplicate = true
		}
		if !newSeen[d.ID] {
			newSeen[d.ID] = true
			newIDs = append(newIDs, d.ID)
			collectorID ^= d.ID
		}
		if dh, ok := r.dimHashesByName[d.FQName]; ok {
			if dh != d.DimHash {
				r.mu.Unlock()
				return ErrDims
			}
			continue
		}
		if dh, ok := newDims[d.FQName]; ok {
			if dh != d.DimHash {
				r.mu.Unlock()
				return ErrNewDims
			}
			continue
		}
		newDims[d.FQName] = d.DimHash
		newNames = append(newNames, d.FQName)
	}
	if len(newIDs) == 0 {
		r.mu.Unlock()
		return OK
	}
	if r.collectorsByID[collectorID] {
		r.mu.Unlock()
		return ErrAlreadyRegistered
	}
	if duplicate {
		r.mu.Unlock()
		return ErrDuplicateDesc
	}
	r.collectorsByID[collectorID] = true
	for _, id := range newIDs {
		r.descIDs[id] = true
	}
	for _, n := range newNames {
		r.dimHashesByName[n] = newDims[n]
	}
	r.mu.Unlock()
	return OK
}

// SeedBuiltins adds to r what client_golang's `init` registers in the default registry: the
// process collector's and the Go collector's descriptors (BuiltinIDs, BuiltinNames with
// BuiltinDims) and their collector IDs (BuiltinCollectors).
func (r *Registry) SeedBuiltins() {
	r.mu.Lock()
	for _, id := range BuiltinIDs() {
		r.descIDs[id] = true
	}
	dims := BuiltinDims()
	for i, n := range BuiltinNames() {
		r.dimHashesByName[n] = dims[i]
	}
	for _, c := range BuiltinCollectors() {
		r.collectorsByID[c] = true
	}
	r.mu.Unlock()
}

// BuiltinIDs are the descriptor IDs of the process and Go collectors (configuration C).
func BuiltinIDs() []uint64 {
	return []uint64{
		0x512fd998710995b,
		0x1656dbe17be56c8e,
		0x25ecb62222d45656,
		0x262eac1a08329894,
		0x27c54efad053ac38,
		0x3344a85f7b6c8e8f,
		0x370d8b8ba9508228,
		0x3ae6afd8564ad088,
		0x3e79faf5f9128782,
		0x411d6370a35c0ff3,
		0x43ee38314d0e9d26,
		0x4f8a790dd5db0ffd,
		0x5036f4e6bfcbacb3,
		0x59cff99389bbcab8,
		0x5dcc41232e6f6fcf,
		0x685c04a736f2da00,
		0x69a5f00e0c426211,
		0x6b4103ccc4d2326c,
		0x70eb462430943cff,
		0x769a93a32973af9b,
		0x80adfa8af06370e0,
		0x87989ab99a809acc,
		0x8b08ab44d6d64d78,
		0x8ce99c9889b6fbce,
		0x8f317e9bd37b52b8,
		0x9d3545e5f6f93ba5,
		0x9ec03ad3db5d4289,
		0xa85bf07416d4b8e0,
		0xac4ef85db62472cb,
		0xc5ec13c9ed3ec103,
		0xc87f9396f586162b,
		0xd8075733a79d1e3a,
		0xd9589318aee2aa20,
		0xdb617cf0bc600144,
		0xe39410b0b2ace77d,
		0xe6efe65b451f2f19,
		0xe7d1a41eea0bc77a,
		0xe98ebbd01e4f623a,
	}
}

// BuiltinNames are their fully-qualified names, sorted.
func BuiltinNames() []string {
	return []string{
		"go_gc_duration_seconds",
		"go_gc_gogc_percent",
		"go_gc_gomemlimit_bytes",
		"go_goroutines",
		"go_info",
		"go_memstats_alloc_bytes",
		"go_memstats_alloc_bytes_total",
		"go_memstats_buck_hash_sys_bytes",
		"go_memstats_frees_total",
		"go_memstats_gc_sys_bytes",
		"go_memstats_heap_alloc_bytes",
		"go_memstats_heap_idle_bytes",
		"go_memstats_heap_inuse_bytes",
		"go_memstats_heap_objects",
		"go_memstats_heap_released_bytes",
		"go_memstats_heap_sys_bytes",
		"go_memstats_last_gc_time_seconds",
		"go_memstats_mallocs_total",
		"go_memstats_mcache_inuse_bytes",
		"go_memstats_mcache_sys_bytes",
		"go_memstats_mspan_inuse_bytes",
		"go_memstats_mspan_sys_bytes",
		"go_memstats_next_gc_bytes",
		"go_memstats_other_sys_bytes",
		"go_memstats_stack_inuse_bytes",
		"go_memstats_stack_sys_bytes",
		"go_memstats_sys_bytes",
		"go_sched_gomaxprocs_threads",
		"go_threads",
		"process_cpu_seconds_total",
		"process_max_fds",
		"process_network_receive_bytes_total",
		"process_network_transmit_bytes_total",
		"process_open_fds",
		"process_resident_memory_bytes",
		"process_start_time_seconds",
		"process_virtual_memory_bytes",
		"process_virtual_memory_max_bytes",
	}
}

// BuiltinDims are the names' dimension hashes, in BuiltinNames' order.
func BuiltinDims() []uint64 {
	return []uint64{
		0xf26f282174a16582, // go_gc_duration_seconds
		0x6f193a898d82b57e, // go_gc_gogc_percent
		0x3f946342ef3e2dc1, // go_gc_gomemlimit_bytes
		0xd6ea775f3e57e0a3, // go_goroutines
		0xd1ef65438edd64ca, // go_info
		0xcb9e68d810ea886,  // go_memstats_alloc_bytes
		0x17cc9550218dfec4, // go_memstats_alloc_bytes_total
		0x7123dfe4d102ec69, // go_memstats_buck_hash_sys_bytes
		0xc546633d5f4c2aee, // go_memstats_frees_total
		0x11ada46281e85a2,  // go_memstats_gc_sys_bytes
		0x7c5deb187b85727,  // go_memstats_heap_alloc_bytes
		0x4d92700b6179627e, // go_memstats_heap_idle_bytes
		0x5614f86bbcc71153, // go_memstats_heap_inuse_bytes
		0x4904e5a3507bc880, // go_memstats_heap_objects
		0xf36123dbdf6efbc9, // go_memstats_heap_released_bytes
		0xbd3e7caa8f21ce08, // go_memstats_heap_sys_bytes
		0x73a8a404a2b111fe, // go_memstats_last_gc_time_seconds
		0x318b0ef37cbb1a3f, // go_memstats_mallocs_total
		0xf0f1c70cebad1075, // go_memstats_mcache_inuse_bytes
		0xad60f0b1578fc8c4, // go_memstats_mcache_sys_bytes
		0x245f1e59f37ed4a4, // go_memstats_mspan_inuse_bytes
		0xb85def6346437dc9, // go_memstats_mspan_sys_bytes
		0x84369ece0eb7f645, // go_memstats_next_gc_bytes
		0x60c4c92a200f4c53, // go_memstats_other_sys_bytes
		0x9012115f6f8ae238, // go_memstats_stack_inuse_bytes
		0xf6a0e04a911cd1a,  // go_memstats_stack_sys_bytes
		0xa5ff86d00c9ad67c, // go_memstats_sys_bytes
		0x1602c8428d1addf3, // go_sched_gomaxprocs_threads
		0xf559241e19ae5834, // go_threads
		0x7969c0480bf010ff, // process_cpu_seconds_total
		0xc40e6e0ce638254b, // process_max_fds
		0xa804b284be1ced27, // process_network_receive_bytes_total
		0x5f99f2510c2201d7, // process_network_transmit_bytes_total
		0xdfd12ffdc6d1d772, // process_open_fds
		0xcfa21a2f3ba47cad, // process_resident_memory_bytes
		0x9e3999b4a0663cbd, // process_start_time_seconds
		0xecb155a0ecaa6d63, // process_virtual_memory_bytes
		0x59c47110ce47128e, // process_virtual_memory_max_bytes
	}
}

// BuiltinCollectors are the two collectors' IDs.
func BuiltinCollectors() []uint64 {
	return []uint64{
		0x2af17207bfef49d7, // *prometheus.goCollector
		0x3c6db576c524bad7, // *prometheus.processCollector
	}
}
