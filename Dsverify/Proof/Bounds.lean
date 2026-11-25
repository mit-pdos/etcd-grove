/-
The bounds the dsverify kits' top-level statements are stated at (mit-pdos/etcd-grove#49 fix 5a:
named, no bare literal in a statement). Each statement's `Robust … threads steps` takes them.
-/
module

public import Robustness.Statement

@[expose] public section

namespace Perennial

/-- The step bound of every dsverify kit: executions of fewer than `2 ^ 63` steps. remote's clock
(`examples/lib/remote`) hands out one receipt per step and needs `receiptBound ≤ 2 ^ 63`: its
counters are Go `int64`s/`uint64`s that must not wrap. -/
abbrev remoteStepBound : Nat := 2 ^ 63

/-- The live-thread bound per machine of the kits that run net/rpc over net/http (craq, gryff,
swiftpaxos, epaxos): fewer than `2 ^ 30` live threads. net/http's first initialization (Net's
`net.http.wp_init_first`) needs `threadBound ≤ 2 ^ 30` (the reader-slot pools of
`DefaultServeMux`'s `RWMutex`), and net/rpc's server (`Server.ServeCodec.spec`) `threadBound ≤ 2 ^ 31`
(its `sync.WaitGroup`'s counter is an `int32`). The kits without net/http quantify the thread bound
instead. -/
abbrev rpcThreadBound : Nat := 2 ^ 30

end Perennial
