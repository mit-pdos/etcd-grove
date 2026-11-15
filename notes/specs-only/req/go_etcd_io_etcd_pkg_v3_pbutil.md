# Requirements on `go.etcd.io/etcd/pkg/v3/pbutil` (4b)


## from 3a

**`MustUnmarshalMessage(&raftReq, e.Data)`** (`apply.go:29`): for bytes with `Apply.irrDecodes bs
ir` (3h's), returns with the message holding `ir` (`Apply.irrMsgAt`); it panics otherwise (the
premise excludes it). Used by: `Apply.spec`.
