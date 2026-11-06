---
upstream: none
checked: 2026-11-04
links: []
blocks-proof: no
---

# bbolt: a negative `DB.AllocSize` makes a commit truncate the file below its committed pages

`DB.grow` (`db.go`) computes the new file size as `growSize(db.datasz, sz)`, which is
`sz + db.AllocSize` once the mapping is larger than `AllocSize`. A negative `AllocSize` set by the
user after `Open` makes that target smaller than the current file, and `db.file.Truncate` then
cuts the file, dropping committed pages; a huge `AllocSize` overflows `int` and the target goes
negative (`Truncate` fails with an error).

**Why not an issue:** a precondition etcd meets: `AllocSize` is an exported field users may set,
but nothing documents negative values, and etcd never sets it (it keeps `DefaultAllocSize`); found
by code reading, no test.

## Proof

no: the bbolt spec forbids clients writing `DB`'s exported fields after `Open`, and the database's
fixed fields (`dbFixed`) bound `AllocSize`, which `DB.grow`'s proof needs for `Truncate`'s size.

## Notes

Found 2026-11-04 by the bbolt proof (U4, `DB.grow`). A guard in `growSize` (treat
`AllocSize <= 0` as `DefaultAllocSize`) would remove it.
