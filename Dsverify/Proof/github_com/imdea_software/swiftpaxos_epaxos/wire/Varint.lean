/-
`epaxos`'s varints (`epaxos/varint.go`): `epaxos.putVarint.spec_holds` (`Varint/PutVarint.lean`)
and `epaxos.readVarint.spec_holds` (`Varint/ReadVarint.lean`), from the internal specs of
`putUvarint` (`Varint/PutUvarint.lean`) and `readUvarint` (`Varint/ReadUvarint.lean`, over
`wp_ReadByte_wf`, `Varint/ReadByte.lean`, and the decoding facts of `Varint/Decode.lean`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Varint.PutVarint
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.wire.Varint.ReadVarint
