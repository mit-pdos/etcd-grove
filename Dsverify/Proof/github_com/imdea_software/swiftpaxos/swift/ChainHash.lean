/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/ChainHash.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Chained and start-marked SHA-256 hashes over command ids: moved to Spec/swift/Hash.lean (change
log C9: `Inv.lean`'s `pathHashes` is start-marked and `checksum_path`/`checksum_deps` are proved
in place). This module re-exports them.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv
