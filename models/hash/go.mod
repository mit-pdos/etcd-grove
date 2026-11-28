// The Go model of the standard library's hash/crc32 (its three arch hooks): files of package crc32,
// spliced into the real package by goose's [model] table (Code/hash/crc32.toml; `goose
// model-overlay` for go build/test). This module is never built; it keeps the files out of
// models.lab's `./...`, where they would not compile as a package of their own path.
module models.lab/stdmodels/hash

go 1.27
