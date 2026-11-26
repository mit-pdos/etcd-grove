// The Go model of the standard library's go/token (its IsExported): files of package token,
// spliced into the real package by goose's [model] table (Net/Code/go/token.toml; `goose
// model-overlay` for go build/test). This module is never built; it keeps the files out of
// models.lab's `./...`, where they would not compile as a package of their own path.
module models.lab/stdmodels/go

go 1.27
