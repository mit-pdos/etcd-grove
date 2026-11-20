// Package wallink is the Go evidence of the WAL link Scope (notes/wal-link-scope.md): the claims
// about etcd's WAL and the server's storage wrapper (server/storage/storage.go) that the link from
// the real WAL's proof (layer 1, over fsExt) to the server's WAL contract (layer 2, isWalStorage)
// relies on. Tests only; not translated.
package wallink
