// The Go model of the standard library's os (Code/os.toml's [model] table: the file layout, the
// models of the functions over the Linux file extension fsExt, and its primitive stubs): files of
// package os, spliced into the real package by goose (`goose model-overlay` for go build/test). This
// module is never built; it keeps the files out of models.lab's `./...`, where they would not
// compile as a package of their own path.
module models.lab/stdmodels/os

go 1.27
