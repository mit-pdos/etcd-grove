-- The copy for the part `KvRaft/` of `Net/ManualProof/net.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The (empty) module `Net/GeneratedProof/net.lean` imports: every type of `net` the model reaches is
translated, so goose emits its instances. (Until etcd-grove#58, 2026-11-25, the instances of the
trusted `UDPConn` layout, from the hand-stated `net.UdpFieldAssumptions`.)
-/
module

public import Perennial.Proof.ProofPrelude
public import GooseLang.Ext.Net.Impl

@[expose] public section
