/-
The initialization of `github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server2` (hand-written,
not generated: `etc/dsv/swiftpaxos.py`'s `PKGS` leaves the kit's programs out, their first run
handing the machine owned resources; notes/dsv-swiftpaxos.md, "State (twelfth session)", the
boot). For now its package fact (`Base.lean`), which the program's generated `PkgTable.lean`
imports through this module; the machine's first-run boot proof is to come here.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.cmd.server2.Base
