/-
# `pkg/v3/pbutil`: protobuf helpers that panic on failure (batch 4b)

`MustMarshalMessage(m)` and `MustUnmarshalMessage(um, data)` are `proto.Marshal`/`proto.Unmarshal`
(2a's `Proto` boundary) that panic on an error. Their specs are stated in `Proto`'s vocabulary
(`msgAt`, `encodes`, `marshalOk`, `Content.fits`): no vocabulary of their own. The premise that
rules the panic out is the caller's: the message marshals (`marshalOk`, and `fits`), or the bytes
encode a message of the type (`encodes`), which each caller has from its protocol (a committed
entry's bytes were marshalled by its proposer: 3h's `irrDecodes`, R1's `committedLb_confDecodes`).

Users: the apply thread (`apply.go:29`, `applyConfChange`: `MustUnmarshalMessage` of an entry's
data), rafthttp's encoders (`msg_codec.go:40`, `msgappv2_codec.go`, `pipeline.go:99`:
`MustMarshalMessage` of a raft message) and decoder (`msgappv2_codec.go`: `MustUnmarshalMessage` of
an entry), the WAL and the snapshotter (2e). Snippets: `examples/specreq/pkgleaves/pbutil.go`
(`ReqMarshalRoundTrip`, `ReqApplyDecode`).
-/
module

public import GeneratedProof.go_etcd_io.etcd.pkg.v3.pbutil
public import Spec.PkgInit.go_etcd_io.etcd.pkg.v3.pbutil
public import Spec.google_golang_org.protobuf.proto.Api

@[expose] public section
