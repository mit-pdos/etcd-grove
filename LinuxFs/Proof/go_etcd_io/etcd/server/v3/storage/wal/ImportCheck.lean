/-
**The import check of the part's WAL proofs** (2026-11-13; `notes/wal-fsext-plan.md`, §8, "part
copies"). The real WAL's code proofs need, in one module, the part's translation of the WAL (over the
part's `os` and its copy of raft's root package), the WAL vocabulary their posts are stated in, the W1
layer (`walInv`, `walInv_crash`) and the protobuf specs of `walpb`'s records. The vocabulary's main-tree
modules reach the main raft root and `os`, whose names the part declares again; the part imports the
generated copies of them instead (`etc/gen-part-copies.py`). This module builds only if the
combination does: no proof, a few names elaborated together. Kept until the part dissolves (the `os`
promotion).
-/
module

public import LinuxFs.GeneratedProof.go_etcd_io.etcd.server.v3.storage.wal
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalHist
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalEncRecs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalEncFold
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalReadAllPost
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalViews
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Inv
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Crash
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Codec
public import LinuxFs.Proof.google_golang_org.protobuf.proto.SizePb
public import LinuxFs.Proof.google_golang_org.protobuf.proto.MarshalPb
public import LinuxFs.Proof.google_golang_org.protobuf.proto.UnmarshalPb
public import LinuxFs.Proof.google_golang_org.protobuf.proto.MarshalAppendCachedRecord

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs.ImportCheck

open WalEnc

/-! The WAL's translation, the vocabulary, the encoding/fold layer and the W1 layer, together. -/

example := @go_etcd_io.etcd.server.v3.storage.wal.WAL
example := @StorContents
example := @walFresh
example := @walReadAllOk
example := @readAllFold
example := @walInv
example := @walInv_crash

end WalFs.ImportCheck
end EtcdGrove
end Perennial
