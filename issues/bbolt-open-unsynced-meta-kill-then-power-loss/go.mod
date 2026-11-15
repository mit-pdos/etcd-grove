module boltfix

go 1.25.0

require go.etcd.io/bbolt v1.5.0

require golang.org/x/sys v0.45.0 // indirect

// A checkout of etcd-io/bbolt at the commit under test (622eada for the failing run).
replace go.etcd.io/bbolt => ../bbolt
